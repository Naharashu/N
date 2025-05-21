import math
import random
import sys
import hashlib
from lark import Lark, Transformer, v_args

# === Symbol Table ===
symbol_table = {
    'var': 'keyword',
    'const': 'keyword',
    'define': 'keyword',
    'exit': 'function',
    'split': 'function',
    'sqrt': 'function',
    'cbrt': 'function',
    'lambert': 'function',
    'log2': 'function',
    'log10': 'function',
    'log': 'function',
    'sin': 'function',
    'cos': 'function',
    'tan': 'function',
    'cotan': 'function',
    'abs': 'function',
    'exp': 'function',
    'factorial': 'function',
    'min': 'function',
    'max': 'function',
    'random': 'function',
    'randint': 'function',
    'output': 'function',
    'input': 'function',
    'len': 'function',
    'toUpper': 'function',
    'toLower': 'function',
    'toInt': 'function',
    'toFloat': 'function',
    'toStr': 'function',
    'typeof': 'function',
    'round': 'function',
    'ceil': 'function',
    'floor': 'function',
    'replace': 'function',
    'append': 'function',
    'pop': 'function',
    'sort': 'function',
    'reverse': 'function',
    'md5': 'function',
    'sha256': 'function',
    'sha1': 'function',
    'charCodeAt': 'function',
    'charCodeFrom': 'function',
    'substring': 'function',
    'partof': 'keyword'
}

# === Scope Management ===
vars = {'pi': 3.14159265, 'e': 2.71828183, 'phi': 1.61803399}
scope_stack = [{}]
consts = {}
mod_vars = {}
mod_funcs = {}
vars_stack = []
funcs = {}

def enter_scope():
    scope_stack.append({})

def exit_scope():
    if len(scope_stack) > 1:
        scope_stack.pop()

def find_variable(name):
    for scope in reversed(scope_stack):
        if name in scope:
            return scope[name]
    if name in vars:
        return vars[name]
    if name in consts:
        return consts[name]
    raise NameError(f"Variable '{name}' not defined in current scope")

def update_variable(name, value, is_const=False):
    if name in scope_stack[-1]:
        if name in consts:
            raise ValueError(f"Cannot reassign constant '{name}'")
        scope_stack[-1][name] = value
    elif any(name in scope for scope in scope_stack[:-1]):
        for scope in reversed(scope_stack[:-1]):
            if name in scope:
                if name in consts:
                    raise ValueError(f"Cannot reassign constant '{name}'")
                scope[name] = value
                break
    else:
        scope_stack[-1][name] = value
        if is_const:
            consts[name] = value

# === Trigonometric Functions in Degrees ===
def sin_deg(x):
    return math.sin(math.radians(x))

def cos_deg(x):
    return math.cos(math.radians(x))

def tan_deg(x):
    return math.tan(math.radians(x))

def cotan_deg(x):
    return 1 / math.tan(math.radians(x))

# === Lark Grammar ===
grammar = r"""

    %import common.WS
    
    // Спеціальні символи
    QUESTION: "?"
    COLON: ":"
    DOT: "."
    COMMA: ","
    SEMI: ";"
    LPAREN: "("
    RPAREN: ")"
    LBRACE: "{"
    RBRACE: "}"
    LBRACK: "["
    RBRACK: "]"
    
    // Оператори
    OP: "+=" | "-=" | "*=" | "/=" | "^=" | ">>" | "<<"
    LOGIC: "==" | "!==" | "<" | ">" | ">=" | "<=" | "is" | "partof"
    AND: "&&"
    OR: "||"
    
    // Літерали
    NUMBER: /\d*\.?\d+/
    STRING: /"[^"]*"|'[^']*'/
    BOOL: "true" | "false"
    ID: /[a-zA-Z_][a-zA-Z_0-9]*/
    
    // Коментарі та пробіли
    COMMENT: /\/\/[^\n]*/
    %ignore COMMENT
    %ignore WS

    program: statements

    statements: statement*
    
    statement: expression (SEMI)?

    block: "{" statements "}"

    array: "[" elements? "]"

    elements: element ("," element)*

    element: NUMBER
            | STRING
            | BOOL
            | expression

    dict: "{" dict_pairs? "}"

    dict_pairs: dict_pair ("," dict_pair)*

    dict_pair: STRING ":" element

    expression: define
               | return_stmt
               | lambda
               | import_stmt
               | if_exp
               | ternary
               | try_catch
               | while_loop
               | always_do
               | raise_stmt
               | continue_stmt
               | break_stmt
               | pass_stmt
               | for_loop
               | foreach_loop
               | assign
               | plain_assign
               | new_assign
               | arr_index
               | logic_expr
               | call
               | mod_var
               | mod_func
               | term

    define: "define" ID "(" params? ")" block

    return_stmt: "return" expression

    lambda: "lambda" "(" params? ")" block

    import_stmt: "import" STRING

    if_exp: "if" cond block ("otherwise" block | "else" block)?

    ternary: cond QUESTION expression COLON expression

    try_catch: "try" block "catch" "(" ID ")" block

    while_loop: "while" cond block

    always_do: "always" "do" block

    raise_stmt: "raise" expression

    continue_stmt: "continue"

    break_stmt: "break"

    pass_stmt: "pass"

    for_loop: "for" "(" ID "," expression "," expression ")" block

    foreach_loop: "foreach" "(" ID "partof" expression ")" block

    assign: ("var" | "const") ID "=" expression

    plain_assign: ID "=" expression

    new_assign: ID OP expression

    arr_index: ID "[" expression "]"

    logic_expr: expression ("&&" | "||") expression

    cond: "(" cond ("&&" | "||") cond ")"
         | expression LOGIC expression
         | expression

    call: ID "(" arguments? ")"
         | "(" expression ")" "(" arguments? ")" -> lambda_call

    mod_var: ID "." ID

    mod_func: ID "." ID "(" arguments? ")"

    arguments: expression ("," expression)*

    params: param ("," param)*

    param: ID

    term: factor
         | term ("*" | "/" | "^" | "%") factor -> binop

    factor: "-" factor -> neg
           | "+" factor -> pos
           | "(" expression ")"
           | NUMBER
           | STRING
           | BOOL
           | ID
           | array
           | dict
           | "null" -> null


"""

# === Lark Parser ===
parser = Lark(grammar, start='program', parser='lalr')

# === Transformer for AST Evaluation ===
@v_args(inline=True)
class EvalTransformer(Transformer):
    def __init__(self):
        super().__init__()
        self.local_vars_cache = {}

    def number(self, value):
        return float(value) if '.' in str(value) else int(value)

    def string(self, value):
        return value[1:-1]  # Remove quotes

    def bool(self, value):
        return value == 'true'

    def null(self):
        return None

    def id(self, value):
        name = str(value)
        if name in self.local_vars_cache:
            return self.local_vars_cache[name]
        return find_variable(name)

    def array(self, *elements):
        return list(elements)

    def dict(self, *pairs):
        return dict(pairs)

    def dict_pair(self, key, value):
        return (key[1:-1], value)  # Remove quotes from key

    def program(self, *statements):
        result = None
        for stmt in statements:
            result = stmt
        return result

    def block(self, *statements):
        enter_scope()
        result = None
        for stmt in statements:
            result = stmt
            if isinstance(result, tuple) and result[0] in ('return', 'continue', 'break'):
                exit_scope()
                return result
        exit_scope()
        return result

    def define(self, name, params, body):
        name = str(name)
        funcs[name] = ('define', params, body)
        symbol_table[name] = 'define'
        return None

    def lambda_(self, params, body):
        return ('func', params, body)

    def return_stmt(self, expr):
        return ('return', expr)

    def import_stmt(self, modul):
        modul = modul[1:-1]  # Remove quotes
        mod_vars[modul] = {}
        mod_funcs[modul] = {}
        try:
            with open(modul + '.nmod', 'r', encoding='utf-8') as f:
                code = f.read()
            parsed = parser.parse(code)
            enter_scope()
            vars_stack.append(scope_stack[-1].copy())
            scope_stack[-1].update(mod_vars[modul])
            globals()['curmod'] = modul
            self.transform(parsed)
            mod_vars[modul] = scope_stack[-1].copy()
            mod_funcs[modul] = {k: v for k, v in scope_stack[-1].items() if isinstance(v, tuple) and v[0] == 'func'}
            exit_scope()
            scope_stack[-1] = vars_stack.pop()
            del globals()['curmod']
        except FileNotFoundError:
            print(f"Module '{modul}' not found")
        return None

    def mod_var(self, modul, var):
        modul, var = str(modul), str(var)
        if modul in mod_vars and var in mod_vars[modul]:
            return mod_vars[modul][var]
        raise NameError(f"Variable '{var}' not found in module '{modul}'")

    def mod_func(self, modul, func, *args):
        modul, func = str(modul), str(func)
        if modul in mod_funcs and func in mod_funcs[modul]:
            arg_names, body = mod_funcs[modul][func][1], mod_funcs[modul][func][2]
            enter_scope()
            for i, arg in enumerate(args[:len(arg_names)]):
                update_variable(arg_names[i], arg)
            globals()['curmod'] = modul
            result = self.transform(body)
            exit_scope()
            del globals()['curmod']
            return result
        raise NameError(f"Function '{func}' not found in module '{modul}'")

    def neg(self, value):
        return -value

    def pos(self, value):
        return value

    def binop(self, left, op, right):
        op = str(op)
        if op == '+': return left + right
        if op == '-': return left - right
        if op == '*': return left * right
        if op == '/': return left / right
        if op == '^': return left ** right
        if op == '%': return left % right
        raise ValueError(f"Unknown operator: {op}")

    def logic_expr(self, left, op, right):
        op = str(op)
        if op == '&&':
            return left and right
        if op == '||':
            return left or right
        raise ValueError(f"Unknown logic operator: {op}")

    def cond(self, left, op=None, right=None):
        if op is None:
            return left
        op = str(op)
        if op == 'partof' and isinstance(right, (int, float)):
            right = [right]
        if op == '==': return left == right
        if op == '!==': return left != right
        if op == '<': return left < right
        if op == '>': return left > right
        if op == '>=': return left >= right
        if op == '<=': return left <= right
        if op == 'is': return left is right
        if op == 'partof':
            if not isinstance(right, (list, str, tuple)):
                raise ValueError(f"Operator 'partof' expects an iterable, got {type(right).__name__}")
            return left in right
        if op == '&&': return left and right
        if op == '||': return left or right
        raise ValueError(f"Unknown condition operator: {op}")

    def if_exp(self, cond, if_body, else_body=None):
        enter_scope()
        result = if_body if cond else (else_body if else_body else None)
        exit_scope()
        return result

    def ternary(self, cond, true_expr, false_expr):
        return true_expr if cond else false_expr

    def try_catch(self, try_block, var, catch_block):
        try:
            return try_block
        except Exception as e:
            enter_scope()
            update_variable(str(var), str(e))
            result = catch_block
            exit_scope()
            return result

    def while_loop(self, cond, body):
        result = None
        while cond:
            enter_scope()
            block_result = body
            exit_scope()
            if isinstance(block_result, tuple):
                if block_result[0] == 'return':
                    return block_result
                if block_result[0] == 'break':
                    break
                if block_result[0] == 'continue':
                    continue
            result = block_result
        return result

    def always_do(self, body):
        result = None
        while True:
            enter_scope()
            block_result = body
            exit_scope()
            if isinstance(block_result, tuple):
                if block_result[0] == 'return':
                    return block_result
                if block_result[0] == 'break':
                    break
                if block_result[0] == 'continue':
                    continue
            result = block_result
        return result

    def raise_stmt(self, expr):
        raise Exception(expr)

    def continue_stmt(self):
        return ('continue',)

    def break_stmt(self):
        return ('break',)

    def pass_stmt(self):
        return None

    def for_loop(self, var, start, end, body):
        start_val, end_val = start, end
        if not isinstance(start_val, (int, float)) or not isinstance(end_val, (int, float)):
            raise ValueError("For loop start and end must be numbers")
        enter_scope()
        update_variable(str(var), start_val)
        result = None
        step = 1 if start_val <= end_val else -1
        for i in range(int(start_val), int(end_val) + (1 if step > 0 else -1), step):
            update_variable(str(var), i)
            block_result = body
            if isinstance(block_result, tuple):
                if block_result[0] == 'return':
                    exit_scope()
                    return block_result
                if block_result[0] == 'break':
                    break
                if block_result[0] == 'continue':
                    continue
            result = block_result
        exit_scope()
        return result

    def foreach_loop(self, var, iterable, body):
        result = None
        if not isinstance(iterable, (list, str)):
            raise ValueError(f"Expected an iterable in foreach, got {type(iterable).__name__}")
        for item in iterable:
            enter_scope()
            update_variable(str(var), item)
            block_result = body
            exit_scope()
            if isinstance(block_result, tuple):
                if block_result[0] == 'return':
                    return block_result
                if block_result[0] == 'break':
                    break
                if block_result[0] == 'continue':
                    continue
            result = block_result
        return result

    def assign(self, type, name, expr):
        is_const = type == 'const'
        update_variable(str(name), expr, is_const)
        return expr

    def plain_assign(self, name, expr):
        update_variable(str(name), expr)
        return expr

    def new_assign(self, name, op, expr):
        name, op = str(name), str(op)
        res = find_variable(name)
        if name in consts:
            raise ValueError(f"Cannot reassign constant '{name}'")
        if op == '+=': res += expr
        elif op == '-=': res -= expr
        elif op == '*=': res *= expr
        elif op == '/=': res /= expr
        elif op == '^=': res **= expr
        elif op == '>>': res >>= expr
        elif op == '<<': res <<= expr
        else: raise NameError(f"Operation '{op}' is not allowed")
        update_variable(name, res)
        return res

    def arr_index(self, name, index):
        name = str(name)
        arr = find_variable(name)
        if not isinstance(arr, (list, str, dict)):
            raise TypeError(f"Variable '{name}' is not indexable")
        if isinstance(arr, dict):
            if index not in arr:
                raise KeyError(f"Key {index} not found in dict")
            return arr[index]
        if not isinstance(index, (int, float)) or index < 0 or index >= len(arr):
            raise IndexError(f"Index {index} out of range")
        return arr[int(index)]

    def call(self, name, *args):
        name = str(name)
        if name in funcs:
            if funcs[name][0] == 'define':
                _, arg_names, body = funcs[name]
                enter_scope()
                for i, arg in enumerate(args[:len(arg_names)]):
                    update_variable(arg_names[i], arg)
                result = self.transform(body)
                exit_scope()
                return result[1] if isinstance(result, tuple) and result[0] == 'return' else result
        if name == 'output':
            print(*[str(arg) if isinstance(arg, list) else arg for arg in args])
            return None
        if name == 'input':
            prompt = args[0] if args else None
            user_input = input(prompt) if prompt else input()
            try:
                return int(user_input)
            except ValueError:
                return user_input
        if name == 'charCodeAt':
            return ord(args[0])
        if name == 'charCodeFrom':
            return chr(args[0])
        if name == 'substring':
            string, start, end = args
            if not isinstance(string, str):
                raise ValueError(f"Expected a string for substring, got {type(string).__name__}")
            if not isinstance(start, (int, float)) or not isinstance(end, (int, float)):
                raise ValueError("Start and end indices must be numbers")
            return string[int(start):int(end)]
        if name == 'split':
            string, delimiter = args
            return string.split(delimiter)
        if name == 'toUpper':
            return args[0].upper()
        if name == 'toLower':
            return args[0].lower()
        if name == 'toInt':
            return int(args[0])
        if name == 'toFloat':
            return float(args[0])
        if name == 'toStr':
            return str(args[0])
        if name == 'md5':
            return hashlib.md5(args[0].encode()).hexdigest()
        if name == 'sha1':
            return hashlib.sha1(args[0].encode()).hexdigest()
        if name == 'sha256':
            return hashlib.sha256(args[0].encode()).hexdigest()
        if name == 'replace':
            old, new, string = args
            return string.replace(old, new)
        if name == 'sort':
            arr = args[0]
            if not isinstance(arr, list):
                raise ValueError(f"Expected an array for sort, got {type(arr).__name__}")
            arr.sort()
            return arr
        if name == 'reverse':
            arr = args[0]
            if not isinstance(arr, list):
                raise ValueError(f"Expected an array for reverse, got {type(arr).__name__}")
            arr.reverse()
            return arr
        if name == 'exit':
            sys.exit()
        if name == 'typeof':
            if isinstance(args[0], str): return 'string'
            if isinstance(args[0], int): return 'int'
            if isinstance(args[0], float): return 'float'
            if isinstance(args[0], list): return 'array'
            if args[0] is None: return 'null'
            if isinstance(args[0], bool): return 'bool'
            if args[0] == 'function': return 'function'
            raise ValueError(f"Unknown type of {args[0]}")
        if name == 'floor':
            return math.floor(args[0])
        if name == 'ceil':
            return math.ceil(args[0])
        if name == 'round':
            return round(args[0])
        if name == 'append':
            arr, el = args
            if not isinstance(arr, list):
                raise ValueError(f"Expected an array for append, got {type(arr).__name__}")
            arr.append(el)
            return arr
        if name == 'pop':
            arr = args[0]
            index = int(args[1]) if len(args) > 1 else -1
            if not isinstance(arr, list):
                raise ValueError(f"Expected an array for pop, got {type(arr).__name__}")
            if index >= len(arr) or index < -len(arr):
                raise IndexError(f"Index {index} out of range")
            return arr.pop(index)
        if name == 'abs':
            return abs(args[0])
        if name == 'log':
            return math.log(*args)
        if name == 'exp':
            return math.exp(args[0])
        if name == 'sqrt':
            return math.sqrt(args[0])
        if name == 'cbrt':
            return math.copysign(abs(args[0]) ** (1/3), args[0])
        if name == 'sin':
            return sin_deg(args[0])
        if name == 'cos':
            return cos_deg(args[0])
        if name == 'tan':
            return tan_deg(args[0])
        if name == 'cotan':
            return cotan_deg(args[0])
        if name == 'min':
            return min(args)
        if name == 'max':
            return max(args)
        if name == 'random':
            return random.random()
        if name == 'randint':
            return random.randint(int(args[0]), int(args[1]))
        if name == 'len':
            return len(args[0])
        if name == 'log2':
            return math.log2(args[0])
        if name == 'log10':
            return math.log10(args[0])
        if name == 'lambert':
            return args[0] * (math.e ** args[0])
        if name == 'factorial':
            return math.factorial(int(args[0]))
        if 'curmod' in globals() and name in mod_funcs.get(globals()['curmod'], {}):
            arg_names, body = mod_funcs[globals()['curmod']][name][1], mod_funcs[globals()['curmod']][name][2]
            enter_scope()
            for i, arg in enumerate(args[:len(arg_names)]):
                update_variable(arg_names[i], arg)
            result = self.transform(body)
            exit_scope()
            return result
        func_def = None
        for scope in reversed(scope_stack):
            if name in scope and isinstance(scope[name], tuple) and scope[name][0] == 'func':
                func_def = scope[name]
                break
        if func_def is None:
            raise NameError(f"Function '{name}' not defined")
        params, body = func_def[1], func_def[2]
        enter_scope()
        for i, param in enumerate(params[:len(args)]):
            update_variable(str(param), args[i])
        result = self.transform(body)
        exit_scope()
        return result[1] if isinstance(result, tuple) and result[0] == 'return' else result

    def lambda_call(self, expr, *args):
        if isinstance(expr, tuple) and expr[0] == 'func':
            params, body = expr[1], expr[2]
            enter_scope()
            for i, param in enumerate(params[:len(args)]):
                update_variable(str(param), args[i])
            result = self.transform(body)
            exit_scope()
            return result[1] if isinstance(result, tuple) and result[0] == 'return' else result
        raise ValueError("Lambda call must be on a lambda expression")

    def params(self, *params):
        return [str(p) for p in params]

    def param(self, p):
        return str(p)

# === Test Run ===
transformer = EvalTransformer()

while True:
    try:
        code = input("Enter your code: ")
        if code.startswith("run "):
            filename = code[4:].strip()
            with open(filename, "r", encoding='utf-8') as f:
                code = f.read()
        parsed = parser.parse(code)
        transformer.transform(parsed)
    except KeyboardInterrupt:
        print("\nExiting...")
        break
    except Exception as e:
        print(f"Error: {e}")