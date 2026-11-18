"""Generates a recursive-descent C++ parser over the tokens of codon::tok from a PEG grammar.

The grammar format follows pegen:
    @preamble {{ C++ code }}
    rule[Type] (memo):
        | item item ... { action }
        | ...
Items:
    NAME NUMBER STRING NEWLINE INDENT DEDENT ENDMARKER DIRECTIVE EXTERN   token kinds; the value is const Token *
    'text'      an operator, or a hard keyword (a Name token)             const Token *
    "text"      a soft keyword (a Name token with that text)              const Token *
    rule        another rule                                              its type
    SP / NOSP   the next token has / has no whitespace before it          (no value)
    &x !x       lookahead                                                 (no value)
    ?{ expr }   semantic predicate                                        (no value)
    ~           cut: the rule fails if a later item of this alternative fails
    [x]         optional                                                  std::optional<V>
    x* x+       repetition                                                std::vector<V>
    s.x+        gather: x (s x)*                                          std::vector<V>
    (a | b)     group; its alternatives need typed actions {<T> expr}, or all be single tokens (then const Token *)
    n=x         binds the value of x to n for the action
Actions: { expr } or, with a statement block, {{ ...; return value; }}. LOC is the source position of the alternative,
CTX the parse context. Without an action, an alternative of a single item has that item's value.
"""

import re
import sys

TOKEN_KINDS = {"NAME", "NUMBER", "STRING", "NEWLINE", "INDENT", "DEDENT", "ENDMARKER", "DIRECTIVE", "EXTERN"}
KIND_ENUM = {"NAME": "Name", "NUMBER": "Number", "STRING": "String", "NEWLINE": "Newline", "INDENT": "Indent",
             "DEDENT": "Dedent", "ENDMARKER": "EndMarker", "DIRECTIVE": "Directive", "EXTERN": "Extern"}


# ---- grammar reader

class Lexer:
    def __init__(self, text):
        self.text = text
        self.pos = 0

    def skip(self):
        while self.pos < len(self.text):
            c = self.text[self.pos]
            if c in " \t\r\n":
                self.pos += 1
            elif c == "#":
                while self.pos < len(self.text) and self.text[self.pos] != "\n":
                    self.pos += 1
            else:
                break

    def peek(self):
        self.skip()
        return self.text[self.pos] if self.pos < len(self.text) else ""

    def startswith(self, s):
        self.skip()
        return self.text.startswith(s, self.pos)

    def expect(self, s):
        if not self.startswith(s):
            raise SyntaxError(f"expected {s!r} at {self.where()}")
        self.pos += len(s)

    def where(self):
        line = self.text.count("\n", 0, self.pos) + 1
        return f"line {line}: {self.text[self.pos:self.pos + 40]!r}"

    def name(self):
        self.skip()
        m = re.compile(r"[A-Za-z_][A-Za-z_0-9]*").match(self.text, self.pos)
        if not m:
            raise SyntaxError(f"expected a name at {self.where()}")
        self.pos = m.end()
        return m.group(0)

    def string(self):
        self.skip()
        q = self.text[self.pos]
        end = self.text.index(q, self.pos + 1)
        s = self.text[self.pos + 1:end]
        self.pos = end + 1
        return q, s

    def balanced(self, open_, close):
        """The text between balanced brackets; the lexer is at open_."""
        self.expect(open_)
        depth, start = 1, self.pos
        while depth:
            c = self.text[self.pos]
            if c in "\"'":  # C++ string or char literal
                q = c
                self.pos += 1
                while self.text[self.pos] != q:
                    self.pos += 2 if self.text[self.pos] == "\\" else 1
            elif c == open_:
                depth += 1
            elif c == close:
                depth -= 1
            self.pos += 1
        return self.text[start:self.pos - 1]


class Item:
    def __init__(self, kind, **kw):
        self.kind = kind  # token, op, softkw, rule, sp, nosp, and, not, pred, cut, opt, star, plus, gather, group
        self.name = None
        self.__dict__.update(kw)


class Alt:
    def __init__(self, items, action, action_type):
        self.items = items
        self.action = action
        self.action_type = action_type


class Rule:
    def __init__(self, name, type_, memo, alts):
        self.name, self.type, self.memo, self.alts = name, type_, memo, alts


def parse_grammar(text):
    lx = Lexer(text)
    preamble, rules = "", []
    while lx.peek():
        if lx.startswith("@preamble"):
            lx.expect("@preamble")
            lx.expect("{{")
            end = lx.text.index("}}", lx.pos)
            preamble += lx.text[lx.pos:end]
            lx.pos = end + 2
            continue
        name = lx.name()
        type_ = lx.balanced("[", "]")
        memo = False
        if lx.startswith("(memo)"):
            lx.expect("(memo)")
            memo = True
        lx.expect(":")
        rules.append(Rule(name, type_, memo, parse_alts(lx, top=True)))
    return preamble, rules


def parse_alts(lx, top):
    alts = []
    if lx.startswith("|"):
        lx.expect("|")
    while True:
        alts.append(parse_alt(lx, top))
        if lx.startswith("|"):
            lx.expect("|")
            continue
        return alts


def is_rule_start(lx):
    """At the top level, a new rule starts with name[...]: or name[...] (memo):."""
    m = re.compile(r"[A-Za-z_][A-Za-z_0-9]*\s*\[").match(lx.text, lx.pos)
    if not m:
        return False
    # name[...]: ... is a rule; name followed by [ inside an alternative does not happen (optional needs a space).
    save = lx.pos
    lx.name()
    try:
        lx.balanced("[", "]")
        ok = lx.startswith(":") or lx.startswith("(memo)")
    except Exception:
        ok = False
    lx.pos = save
    return ok


def parse_alt(lx, top):
    items, action, action_type = [], None, None
    while True:
        c = lx.peek()
        if c == "" or c == "|" or c == ")" or c == "]":
            break
        if top and is_rule_start(lx):
            break
        if c == "{":
            code = lx.balanced("{", "}")
            if code.startswith("{") and code.endswith("}"):
                action = ("block", code[1:-1])
            else:
                code = code.strip()
                if code.startswith("<"):
                    depth, i = 0, 0
                    while True:
                        depth += {"<": 1, ">": -1}.get(code[i], 0)
                        if depth == 0:
                            break
                        i += 1
                    action_type, code = code[1:i], code[i + 1:].strip()
                action = ("expr", code)
            break
        items.append(parse_item(lx))
    return Alt(items, action, action_type)


def parse_item(lx):
    lx.skip()
    m = re.compile(r"([A-Za-z_][A-Za-z_0-9]*)=(?!=)").match(lx.text, lx.pos)
    bind = None
    if m:
        bind = m.group(1)
        lx.pos = m.end()
    item = parse_prefixed(lx)
    item.name = bind
    return item


def parse_prefixed(lx):
    if lx.startswith("&"):
        lx.expect("&")
        return Item("and", inner=parse_primary(lx))
    if lx.startswith("!"):
        lx.expect("!")
        return Item("not", inner=parse_primary(lx))
    if lx.startswith("?{"):
        lx.expect("?")
        return Item("pred", code=lx.balanced("{", "}"))
    if lx.startswith("~"):
        lx.expect("~")
        return Item("cut")
    prim = parse_primary(lx)
    if lx.text.startswith(".", lx.pos) and prim.kind in ("op", "softkw"):  # gather s.x+
        lx.pos += 1
        elem = parse_primary(lx)
        lx.expect("+")
        return Item("gather", sep=prim, inner=elem)
    if lx.text.startswith("*", lx.pos):
        lx.pos += 1
        return Item("star", inner=prim)
    if lx.text.startswith("+", lx.pos):
        lx.pos += 1
        return Item("plus", inner=prim)
    return prim


def parse_primary(lx):
    c = lx.peek()
    if c == "(":
        lx.expect("(")
        alts = parse_alts(lx, top=False)
        lx.expect(")")
        return Item("group", alts=alts)
    if c == "[":
        lx.expect("[")
        alts = parse_alts(lx, top=False)
        lx.expect("]")
        inner = alts[0].items[0] if len(alts) == 1 and len(alts[0].items) == 1 and not alts[0].action else Item(
            "group", alts=alts)
        return Item("opt", inner=inner)
    if c in "'\"":
        q, s = lx.string()
        return Item("op" if q == "'" else "softkw", text=s)
    n = lx.name()
    if n in TOKEN_KINDS:
        return Item("token", token=n)
    if n == "SP":
        return Item("sp")
    if n == "NOSP":
        return Item("nosp")
    return Item("rule", rule=n)


# ---- code generation

class Gen:
    def __init__(self, rules, hard_keywords):
        self.rules = {r.name: r for r in rules}
        self.hard = hard_keywords
        self.counter = 0

    def fresh(self, prefix):
        self.counter += 1
        return f"_{prefix}{self.counter}"

    def value_type(self, item):
        """The C++ type of the value of an item, or None for items without a value."""
        k = item.kind
        if k in ("token", "op", "softkw"):
            return "const Token *"
        if k == "rule":
            return self.rules[item.rule].type
        if k == "group":
            return self.group_type(item)
        if k == "opt":
            t = self.value_type(item.inner)
            return f"std::optional<{t}>"
        if k in ("star", "plus", "gather"):
            return f"std::vector<{self.value_type(item.inner)}>"
        return None

    def group_type(self, item):
        types = set()
        for alt in item.alts:
            if alt.action:
                if not alt.action_type:
                    raise SyntaxError("a group alternative with an action needs a type: {<T> expr}")
                types.add(alt.action_type)
            elif len(alt.items) == 1 and alt.items[0].kind in ("token", "op", "softkw"):
                types.add("const Token *")
            elif len(alt.items) == 1 and alt.items[0].kind == "rule":
                types.add(self.rules[alt.items[0].rule].type)
            else:
                types.add("bool")
        if len(types) != 1:
            raise SyntaxError(f"group alternatives of different types: {types}")
        return types.pop()

    def token_expr(self, item):
        if item.kind == "token":
            if item.token == "NAME":
                return "expectName()"
            return f"expectKind(Kind::{KIND_ENUM[item.token]})"
        if item.kind == "op":
            if item.text in self.hard:
                return f'expectKeyword("{item.text}")'
            return f'expectOp("{item.text}")'
        return f'expectKeyword("{item.text}")'

    def match_expr(self, item, out):
        """Code that evaluates an item with a value to an std::optional<V> (engaged on success). Emits helper code to out
        and returns the expression."""
        k = item.kind
        if k in ("token", "op", "softkw"):
            return f"tokOpt({self.token_expr(item)})"
        if k == "rule":
            return f"r_{item.rule}()"
        if k == "group":
            g = self.fresh("g")
            t = self.group_type(item)
            out.append(f"auto {g} = [&]() -> std::optional<{t}> {{")
            self.emit_alts(item.alts, t, out, indent="  ")
            out.append("  return std::nullopt;")
            out.append("};")
            return f"{g}()"
        raise SyntaxError(f"no value: {k}")

    def emit_items(self, items, out, ind):
        """Emits the items of an alternative inside a do { } while (false); a failing item breaks out."""
        values = []
        for item in items:
            k = item.kind
            if k == "sp":
                out.append(f"{ind}if (!sp()) break;")
                continue
            if k == "nosp":
                out.append(f"{ind}if (sp()) break;")
                continue
            if k == "cut":
                out.append(f"{ind}_cut = true;")
                continue
            if k == "pred":
                out.append(f"{ind}if (!({item.code})) break;")
                continue
            if k in ("and", "not"):
                helper = []
                e = self.lookahead_expr(item.inner, helper)
                for h in helper:
                    out.append(ind + h)
                p = self.fresh("p")
                out.append(f"{ind}size_t {p} = pos;")
                out.append(f"{ind}bool {p}_ok = bool({e});")
                out.append(f"{ind}pos = {p};")
                out.append(f"{ind}if ({'!' if k == 'and' else ''}{p}_ok) break;")
                continue
            v = self.fresh("v")
            if k == "opt":
                helper = []
                e = self.match_expr(item.inner, helper)
                for h in helper:
                    out.append(ind + h)
                out.append(f"{ind}auto {v} = {e};")
                if item.name:
                    out.append(f"{ind}auto &{item.name} = {v};")
                values.append((v, False))
                continue
            if k in ("star", "plus", "gather"):
                helper = []
                e = self.match_expr(item.inner, helper)
                for h in helper:
                    out.append(ind + h)
                t = self.value_type(item.inner)
                out.append(f"{ind}std::vector<{t}> {v};")
                if k == "gather":
                    sep = self.token_expr(item.sep)
                    out.append(f"{ind}if (auto _e = {e}) {{")
                    out.append(f"{ind}  {v}.push_back(std::move(*_e));")
                    out.append(f"{ind}  while (true) {{")
                    out.append(f"{ind}    size_t _q = pos;")
                    out.append(f"{ind}    if (!{sep}) {{ pos = _q; break; }}")
                    out.append(f"{ind}    auto _f = {e};")
                    out.append(f"{ind}    if (!_f) {{ pos = _q; break; }}")
                    out.append(f"{ind}    {v}.push_back(std::move(*_f));")
                    out.append(f"{ind}  }}")
                    out.append(f"{ind}}}")
                else:
                    out.append(f"{ind}while (true) {{")
                    out.append(f"{ind}  size_t _q = pos;")
                    out.append(f"{ind}  auto _e = {e};")
                    out.append(f"{ind}  if (!_e) {{ pos = _q; break; }}")
                    out.append(f"{ind}  {v}.push_back(std::move(*_e));")
                    out.append(f"{ind}}}")
                if k in ("plus", "gather"):
                    out.append(f"{ind}if ({v}.empty()) break;")
                if item.name:
                    out.append(f"{ind}auto &{item.name} = {v};")
                values.append((v, False))
                continue
            helper = []
            e = self.match_expr(item, helper)
            for h in helper:
                out.append(ind + h)
            out.append(f"{ind}auto {v} = {e};")
            out.append(f"{ind}if (!{v}) break;")
            if item.name:
                out.append(f"{ind}auto &{item.name} = *{v};")
            values.append((v, True))
        return values

    def lookahead_expr(self, item, helper):
        if item.kind in ("token", "op", "softkw"):
            return self.token_expr(item)
        if item.kind == "rule":
            return f"r_{item.rule}()"
        if item.kind == "group":
            g = self.fresh("g")
            helper.append(f"auto {g} = [&]() -> bool {{")
            for alt in item.alts:
                body = []
                self.emit_items(alt.items, body, "    ")
                helper.append("  do {")
                helper.extend(body)
                helper.append("    return true;")
                helper.append("  } while (false);")
            helper.append("  return false;")
            helper.append("};")
            return f"{g}()"
        raise SyntaxError(f"lookahead of {item.kind}")

    def emit_alts(self, alts, rtype, out, indent):
        for alt in alts:
            out.append(f"{indent}{{")
            out.append(f"{indent}  size_t _start = pos;")
            out.append(f"{indent}  bool _cut = false;")
            out.append(f"{indent}  do {{")
            values = self.emit_items(alt.items, out, indent + "    ")
            ind = indent + "    "
            if alt.action:
                kind, code = alt.action
                out.append(f"{ind}[[maybe_unused]] auto LOC = loc(_start);")
                if kind == "block":
                    out.append(f"{ind}return std::optional<{rtype}>([&]() -> {rtype} {{ {code} }}());")
                else:
                    out.append(f"{ind}return std::optional<{rtype}>({code});")
            elif len(values) == 1:
                v, required = values[0]
                out.append(f"{ind}return std::optional<{rtype}>({'*' if required else ''}{v});")
            elif rtype == "bool":
                out.append(f"{ind}return std::optional<bool>(true);")
            else:
                raise SyntaxError("an alternative of several items needs an action")
            out.append(f"{indent}  }} while (false);")
            out.append(f"{indent}  pos = _start;")
            out.append(f"{indent}  if (_cut) return std::nullopt;")
            out.append(f"{indent}}}")

    def rule(self, r):
        out = [f"std::optional<{r.type}> Parser::r_{r.name}() {{"]
        if r.memo:
            out.append(f"  if (memo_{r.name}.empty()) memo_{r.name}.resize(toks.size() + 1);")
            out.append(f"  if (auto &_m = memo_{r.name}[pos]; _m.end) {{")
            out.append(f"    pos = _m.end - 1;")
            out.append(f"    return _m.value;")
            out.append(f"  }}")
            out.append(f"  size_t _memoStart = pos;")
            out.append(f"  auto _result = [&]() -> std::optional<{r.type}> {{")
            self.emit_alts(r.alts, r.type, out, "    ")
            out.append("    return std::nullopt;")
            out.append("  }();")
            out.append(f"  memo_{r.name}[_memoStart] = MemoEntry<{r.type}>{{uint32_t(pos + 1), _result}};")
            out.append("  return _result;")
        else:
            self.emit_alts(r.alts, r.type, out, "  ")
            out.append("  return std::nullopt;")
        out.append("}")
        return "\n".join(out)


def main():
    grammar_file, out_file = sys.argv[1], sys.argv[2]
    text = open(grammar_file).read()
    preamble, rules = parse_grammar(text)
    hard = re.search(r"//\s*HARD_KEYWORDS:(.*)", preamble).group(1).split()
    gen = Gen(rules, set(hard))
    decls = []
    for r in rules:
        decls.append(f"  std::optional<{r.type}> r_{r.name}();")
        if r.memo:
            decls.append(f"  std::vector<MemoEntry<{r.type}>> memo_{r.name};")
    code = [
        "// Generated by generate.py. Do not edit.",
        preamble,
        "namespace codon::tokparser {",
        "struct Parser : ParserBase {",
        "  using ParserBase::ParserBase;",
        *decls,
        "};",
        *[gen.rule(r) for r in rules],
        "} // namespace codon::tokparser",
    ]
    open(out_file, "w").write("\n".join(code) + "\n")


if __name__ == "__main__":
    main()
