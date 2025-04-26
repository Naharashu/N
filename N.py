import ply.lex as lex
import ply.yacc as yacc
import math
import random
import sys

# === Symbol Table ===
symbol_table = {
    'var': 'integer',
    'sqrt': 'function',
    'cbrt': 'function',
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
    'randfloat': 'function',
    'output': 'function',
    'input': 'function',
    'len': 'function'
}

# === Trigonometric Functions in Degrees ===
def sin_deg(x):
    return math.sin(math.radians(x))

def cos_deg(x):
    return math.cos(math.radians(x))

def tan_deg(x):
    return math.tan(math.radians(x))

def cotan_deg(x):
    return 1 / math.tan(math.radians(x))

def symbol_lookup(identifier):
    return symbol_table.get(identifier, 'unknown')

vars = {'pi': 3.14159265, 'e': 2.71828183, 'phi': 1.61803399}
funcs = {}

# === Lexer ===
tokens = (
    'NUMBER', 'STRING', 'VAR', 'FOR', 'FUNC', 'RETURN', 'IF', 'OTHERWISE', 'WHILE', 'ELSE', 'ID',
    'PLUS', 'MINUS', 'MULTIPLE', 'DIVIDE', 'POW', 'MOD',
    'LPAREN', 'RPAREN', 'LBRACKET', 'LBRACK', 'RBRACK', 'RBRACKET',
    'COMMA', 'EQ', 'EE', 'NEQ', 'LT', 'GT', 'GTE', 'LTE', 'op', 'IS', 'IN', 'DO', 'ALWAYS', 'TWODOTS', 'QUE', 'IMPORT'
)

t_PLUS = r'\+'
t_MINUS = r'-'
t_MULTIPLE = r'\*'
t_DIVIDE = r'/'
t_POW = r'\^'
t_MOD = r'\%'
t_LPAREN = r'\('
t_RPAREN = r'\)'
t_LBRACKET = r'\{'
t_RBRACKET = r'\}'
t_LBRACK = r'\['
t_RBRACK = r'\]'
t_EQ = r'='
t_TWODOTS = r'\:'
t_QUE = r'\?'
t_NEQ = r'!=='
t_EE = r'=='
t_LT = r'<'
t_GT = r'>'
t_GTE = r'>='
t_LTE = r'<='
t_COMMA = r','

def t_op(t):
    r'\+\=|-\=|\*\=|\/\='
    return t

def t_IMPORT(t):
    r'import'
    return t
    
def t_ALWAYS(t):
	r'always'
	return t
    
def t_DO(t):
	r'do'
	return t
	
def t_VAR(t):
    r'var'
    return t

def t_FOR(t):
    r'for'
    return t

def t_FUNC(t):
    r'func'
    return t

def t_IF(t):
    r'if'
    return t

def t_OTHERWISE(t):
    r'otherwise'
    return t
    
def t_ELSE(t):
	r'else'
	return t

def t_RETURN(t):
    r'return'
    return t

def t_IS(t):
    r'is'
    return t

def t_IN(t):
    r'partof'
    return t

def t_WHILE(t):
    r'while'
    return t

def t_ID(t):
    r'[a-zA-Z_][a-zA-Z_0-9]*'
    t.value = (t.value, symbol_lookup(t.value))
    return t

def t_NUMBER(t):
    r'\d*\.?\d+'
    t.value = float(t.value) if '.' in t.value else int(t.value)
    return t

def t_STRING(t):
    r'"[^"]*"|\'[^\']*\''
    t.value = t.value[1:-1]
    return t

def t_COMMENT(t):
    r'\/\/[^\n]*'
    pass

def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)

t_ignore = ' \t'

def t_error(t):
    print(f"Illegal character '{t.value[0]}' at line {t.lineno}")
    t.lexer.skip(1)

lexer = lex.lex()
lexer.lineno = 1 

# === Parser ===
start = 'statements'

precedence = (
    ('left', 'COMMA'),
    ('left', 'PLUS', 'MINUS'),
    ('left', 'MULTIPLE', 'DIVIDE'),
    ('right', 'POW', 'MOD'),
    ('right', 'UMINUS', 'UPLUS'),
    ('nonassoc', 'EQ'),
    ('nonassoc', 'LPAREN', 'RPAREN', 'LBRACKET', 'RBRACKET'),
    ('nonassoc', 'FUNC', 'VAR', 'FOR', 'RETURN', 'IF', 'OTHERWISE', 'ELSE' ,'WHILE'),
    ('nonassoc', 'op', 'IN')
)

def p_block(p):
    'block : LBRACKET statements RBRACKET'
    p[0] = ('block', p[2])

def p_array(p):
    'array : LBRACK elements RBRACK'
    els = p[2]
    p[0] = ('array', els)

def p_elements_multiple(p):
    'elements : elements COMMA element'
    p[0] = p[1] + [p[3]]

def p_elements_single(p):
    'elements : element'
    p[0] = [p[1]]

def p_element(p):
    '''element : NUMBER
               | STRING
               | expression'''
    p[0] = p[1]

def p_statements_multiple(p):
    'statements : statements expression'
    p[0] = p[1] + [p[2]]

def p_statements_single(p):
    'statements : expression'
    p[0] = [p[1]]

def p_expression_binop(p):
    '''expression : expression PLUS term
                  | expression MINUS term'''
    p[0] = (p[2], p[1], p[3])

def p_term_binop(p):
    '''term : term MULTIPLE factor
            | term DIVIDE factor
            | term POW factor
            | term MOD factor'''
    p[0] = (p[2], p[1], p[3])
    
def p_expression_term(p):
    'expression : term'
    p[0] = p[1]

def p_term_factor(p):
    'term : factor'
    p[0] = p[1]

def p_factor_unary(p):
    '''factor : MINUS factor %prec UMINUS
              | PLUS factor %prec UPLUS'''
    p[0] = ('neg', p[2]) if p[1] == '-' else p[2]

def p_factor_group(p):
    'factor : LPAREN expression RPAREN'
    p[0] = p[2]

def p_factor_number(p):
    'factor : NUMBER'
    p[0] = p[1]

def p_factor_string(p):
    'factor : STRING'
    p[0] = p[1]

def p_factor_id(p):
    'factor : ID'
    p[0] = p[1]

def p_factor_array(p):
    'factor : array'
    p[0] = p[1]

def p_expression_return(p):
    'expression : RETURN retval'
    p[0] = ('return', p[2])
    
def p_retval_multiple(p):
    'retval : LPAREN retval COMMA expression RPAREN'
    p[0] = p[1] + [p[3]]
    
def p_retval_single(p):
    'retval : expression'
    p[0] = p[1]
    
def p_import(p):
    'expression : IMPORT STRING'
    p[0] = ('import', p[2])

def p_expression_if(p):
    '''expression : IF cond block
                  | IF cond block OTHERWISE block
                  | IF cond block ELSE block'''
    cond = p[2]
    ifbody = p[3]
    otherbody = None if len(p) == 4 else p[5]
    p[0] = ('ifExp', cond, ifbody, otherbody)
    
def p_ternar(p):
    'expression : cond QUE expression TWODOTS expression'
    cond = p[1]
    body = p[3]
    elsebody = p[5]
    p[0] = ('ternar', cond, body, elsebody)
    
    
def p_expression_while(p):
    'expression : WHILE cond block'
    cond = p[2]
    body = p[3]
    p[0] = ('while', cond, body)
    
def p_expression_alwaysdo(p):
	'expression : ALWAYS DO block'
	body = p[3]
	p[0] = ('alwaysDo', body)

def p_cond(p):
    '''cond : expression logic expression'''
    p[0] = ('cond', p[1], p[2], p[3])

def p_logic(p):
    '''logic : EE
             | NEQ
             | LT
             | GT
             | GTE
             | LTE
             | IS
             | IN'''
    p[0] = p[1]

def p_factor_function(p):
    '''factor : ID LPAREN RPAREN
              | ID LPAREN arguments RPAREN'''
    name, typ = p[1]
    args = [] if len(p) == 4 else p[3]
    if typ == 'function' or name in funcs:
        p[0] = ('call', name, args)
    else:
        print(f"Error: '{name}' is not a function")
        p[0] = ('error', name)

def p_arguments_multiple(p):
    'arguments : arguments COMMA expression'
    p[0] = p[1] + [p[3]]

def p_arguments_single(p):
    'arguments : expression'
    p[0] = [p[1]]

def p_expression_func_def(p):
    'expression : FUNC ID LPAREN params RPAREN block'
    name, _ = p[2]
    params = p[4]
    body = p[6]
    funcs[name] = (params, body)
    symbol_table[name] = 'function'
    p[0] = ('ownfunc', name, params, body)

def p_params_multiple(p):
    'params : params COMMA param'
    name, _ = p[3]
    p[0] = p[1] + [name]

def p_params_single(p):
    'params : param'
    name, _ = p[1]
    p[0] = [name]

def p_params_empty(p):
    'params :'
    p[0] = []

def p_param(p):
    'param : ID'
    p[0] = p[1]

def p_expression_for(p):
    'expression : FOR LPAREN ID COMMA expression COMMA expression RPAREN block'
    name, _ = p[3]
    p[0] = ('for', name, p[5], p[7], p[9])

def p_expression_assign(p):
    'expression : VAR ID EQ expression'
    name, _ = p[2]
    val = p[4]
    p[0] = ('assign', name, val)

def p_expression_newAssign(p):
    'expression : ID op expression'
    name, _ = p[1]
    opera = p[2]
    val = p[3]
    p[0] = ('newAssign', name, val, opera)

def p_error(p):
    if p:
        print(f"Syntax error at token '{p.value}' (type: {p.type}) on line {p.lineno}")
        while p and p.type not in ('\n', 'RBRACKET', 'FUNC', 'VAR', 'FOR', 'ID'):
            p.lexer.skip(1)
            p = p.lexer.token()
    else:
        print("Syntax error at EOF")

parser = yacc.yacc()

# === Interpreter ===
def eval_ast(node):
    if isinstance(node, (int, float, str, list)):
        return node
    if node[0] == 'error':
        raise NameError(f"'{node[1]}' is not a function")
    if node[0] == 'neg':
        return -eval_ast(node[1])
    if node[0] == 'import':
        modul = node[1]
        try:
            with open(modul + '.nmod', 'r') as f:
                code = f.read()
            if result:
                for expr in result:
                    eval_ast(expr)
        except FileNotFoundError:
            print(f"Module '{modul}' not found")
        return None
    if node[0] == 'array':
        els = node[1]
        return [eval_ast(el) for el in els]
    if node[0] == 'block':
        _, statements = node
        result = None
        for stmt in statements:
            result = eval_ast(stmt)
        return result
    if node[0] == 'return':
        return eval_ast(node[1])
    if node[0] == 'alwaysDo':
        body = node[1]
        while True:
            eval_ast(body)
    if node[0] == 'ternar':
        cond = node[1]
        body = node[2]
        elsebody = node[3]
        if cond[0] == 'cond':
            left = eval_ast(cond[1])
            op = cond[2]
            right = eval_ast(cond[3])
            if op == '==':
                cond1 = left == right
            elif op == '!==':
                cond1 = left != right
            elif op == '<':
                cond1 = left < right
            elif op == '>':
                cond1 = left > right
            elif op == '>=':
                cond1 = left >= right
            elif op == '<=':
                cond1 = left <= right
            elif op == 'is':
                cond1 = left is right
            elif op == 'partof':
                cond1 = left in right
            else:
                raise ValueError(f"Unknown operator: {op}")
            
        if cond1:
            return eval_ast(body)
        else:
            return eval_ast(elsebody)
    if node[0] == 'ifExp':
        cond = node[1]
        body1 = node[2]
        body2 = node[3]
        if cond[0] == 'cond':
            left = eval_ast(cond[1])
            op = cond[2]
            right = eval_ast(cond[3])
            if op == '==':
                cond1 = left == right
            elif op == '!==':
                cond1 = left != right
            elif op == '<':
                cond1 = left < right
            elif op == '>':
                cond1 = left > right
            elif op == '>=':
                cond1 = left >= right
            elif op == '<=':
                cond1 = left <= right
            elif op == 'is':
                cond1 = left is right
            elif op == 'partof':
                cond1 = left in right
        if cond1:
            return eval_ast(body1)
        elif body2 is not None:
            return eval_ast(body2)
        return None
    if node[0] == 'while':
        cond = node[1]
        body = node[2]
        while True:
            if cond[0] == 'cond':
                left = eval_ast(cond[1])
                op = cond[2]
                right = eval_ast(cond[3])
                if op == '==':
                    cond1 = left == right
                elif op == '!==':
                    cond1 = left != right
                elif op == '<':
                    cond1 = left < right
                elif op == '>':
                    cond1 = left > right
                elif op == '>=':
                    cond1 = left >= right
                elif op == '<=':
                    cond1 = left <= right
                elif op == 'is':
                    cond1 = left is right
                elif op == 'partof':
                    cond1 = left in right
                else:
                    raise ValueError(f"Unknown operator: {op}")
            if not cond1:
                break
            eval_ast(body)
        return None
    if node[0] == 'assign':
        _, name, expr = node
        val = eval_ast(expr)
        vars[name] = val
        return val
    if node[0] == 'newAssign':
        name = node[1]
        val = eval_ast(node[2])
        opera = node[3]
        if name not in vars:
            raise NameError(f"Variable '{name}' is not defined")
        res = vars[name]
        if opera == '+=':
            res += val
        elif opera == '-=':
            res -= val
        elif opera == '*=':
            res *= val
        elif opera == '/=':
            res /= val
        else:
            raise NameError(f"Operation '{opera}' is not allowed")
        vars[name] = res
        return res
    if node[0] == 'call':
        name, args = node[1], node[2]
        args = [eval_ast(a) for a in args]
        if name == 'output':
            print(*[str(arg) if isinstance(arg, list) else arg for arg in args], file=sys.stderr, flush=True)
            return None
        if name == 'input':
            user_input = input(args[0])
            try:
                return int(user_input)
            except ValueError:
                return user_input
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
        if name == 'randfloat':
            return random.random()
        if name == 'factorial':
            res = args[0]
            if not isinstance(res, int) or res < 0:
                raise ValueError("Factorial expects a non-negative integer")
            if res == 0 or res == 1:
                return 1
            result = 1
            for i in range(2, res + 1):
                result *= i
            return result
        if name in funcs:
            arg_names, body = funcs[name]
            old_vars = vars.copy()
            for i in range(min(len(arg_names), len(args))):
                vars[arg_names[i]] = args[i]
            result = eval_ast(body)
            vars.clear()
            vars.update(old_vars)
            return result
        raise NameError(f"Function '{name}' is not defined")
    if node[0] == 'ownfunc':
        return None
    if node[0] == 'for':
        _, var, start, end, body = node
        start_val = eval_ast(start)
        end_val = eval_ast(end)
        if not isinstance(start_val, int) or not isinstance(end_val, int):
            raise ValueError("For loop start and end must be integers")
        old_vars = vars.copy()
        if start_val <= end_val:
            for i in range(start_val, end_val + 1):
                vars[var] = i
                eval_ast(body)
        else:
            for i in range(start_val, end_val - 1, -1):
                vars[var] = i
                eval_ast(body)
        vars.clear()
        vars.update(old_vars)
        return None
    if isinstance(node, tuple) and len(node) == 2 and isinstance(node[1], str):
        name, _ = node
        if name in vars:
            return vars[name]
        raise NameError(f"Variable '{name}' is not defined")
    if isinstance(node, tuple) and len(node) == 3:
        op, left, right = node
        left_val = eval_ast(left)
        right_val = eval_ast(right)
        if op == '+':
            return left_val + right_val
        if op == '-':
            return left_val - right_val
        if op == '*':
            return left_val * right_val
        if op == '/':
            return left_val / right_val
        if op == '^':
            return left_val ** right_val
        if op == '%':
            return left_val % right_val
    raise ValueError(f"Unknown node: {node}")
    
    
while True:
    # === Test Run ===
    code = input("Enter your code: ")
    
    if code.startswith("run "):
        filename = code[4:].strip()
        with open(filename, "r") as f:
            code = f.read()
        

    # Test Parser
    result = parser.parse(code)

    if result is None:
        print("Parsing failed due to syntax error")
    else:
        for expr in result:
            eval_ast(expr)