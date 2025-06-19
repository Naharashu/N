from lark import Lark, Transformer, v_args

grammer = """
start: statement*

%import common.WS
%import common.NUMBER -> NUM
%import common.CNAME -> ID
%import common.ESCAPED_STRING -> STRING
DOT: "."

int: NUM
    | "+" NUM -> int
    | "-" NUM -> int

statement: ID "=" factor -> assign
         | WRITE expr    -> write

WRITE: "write"

expr: term
    | expr "+" term      -> add
    | expr "-" term      -> sub

term: factor
    | term "*" factor    -> mul
    | term "/" factor    -> div

factor: int
      | ID               -> var
      | STRING
      | "(" expr ")"

%ignore WS
"""

vars = {}

class lang(Transformer):
    def start(self, *statements):
        return statements

    def NUM(self, n):
        return float(n)

    @v_args(inline=True)
    def int(self, *items):
        if len(items) == 1:
            return items[0]
        else:
            sign, number = items
            number = float(number)
            return number if sign == '+' else -number

    def STRING(self, s):
        return str(s)[1:-1]

    def ID(self, id_token):
        return str(id_token)

    def var(self, name):
        name = str(name)
        if name in vars:
            return vars[name]
        else:
            raise NameError(f"Variable '{name}' is not defined")

    @v_args(inline=True)
    def add(self, a, b): return a + b
    @v_args(inline=True)
    def sub(self, a, b): return a - b
    @v_args(inline=True)
    def mul(self, a, b): return a * b
    @v_args(inline=True)
    def div(self, a, b): return a / b

    def assign(self, items):
        ID, VAL = items
        vars[ID] = VAL
        return None

    @v_args(inline=True)
    def write(self, val):
        print(val)
        return None

parser = Lark(grammer, parser='lalr')

while True:
    try:
        code = input("> ")
        tree = parser.parse(code)
        interpreter = lang()
        interpreter.transform(tree)
    except Exception as e:
        print(f'Error: {e}')
