import ply.lex as lex
import ply.yacc as yacc
import math
import random
import sys
import hashlib

lines = []

# === Symbol Table ===
symbol_table = {
    'var': 'keyword',
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
    'charCodeAt': 'function',
    'charCodeFrom': 'function',
    'substring': 'function'
}

mod_vars = {}
vars_stack = []
mod_funcs = {}

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
    'NUMBER', 'STRING', 'TRUE', 'FALSE', 'VAR', 'FOR', 'FUNC', 'RETURN', 'IF', 'OTHERWISE', 'WHILE', 'ELSE', 'ID',
    'PLUS', 'MINUS', 'MULTIPLE', 'DIVIDE', 'POW', 'MOD', 'DOT',
    'LPAREN', 'RPAREN', 'LBRACKET', 'LBRACK', 'RBRACK', 'RBRACKET',
    'COMMA', 'EQ', 'EE', 'NEQ', 'LT', 'GT', 'GTE', 'LTE', 'op', 'IS', 'IN', 'DO', 'ALWAYS', 'TWODOTS', 'QUE', 'IMPORT', 'SEMI',
    'CONTINUE', 'BREAK', 'PASS', 'AND', 'OR'
)

t_PLUS = r'\+'
t_MINUS = r'-'
t_MULTIPLE = r'\*'
t_DIVIDE = r'/'
t_POW = r'\^'
t_MOD = r'\%'
t_DOT = r'\.'
t_LPAREN = r'\('
t_RPAREN = r'\)'
t_LBRACKET = r'\{'
t_RBRACKET = r'\}'
t_LBRACK = r'\['
t_RBRACK = r'\]'
t_EQ = r'='
t_TWODOTS = r'\:'
t_SEMI = r'\;'
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

def t_CONTINUE(t):
    r'continue'
    return t

def t_BREAK(t):
    r'break'
    return t

def t_PASS(t):
    r'pass'
    return t

def t_AND(t):
    r'&&'
    return t

def t_OR(t):
    r'\|\|'
    return t

def t_IMPORT(t):
    r'import'
    return t

def t_TRUE(t):
    r'true'
    return t

def t_FALSE(t):
    r'false'
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
    r'[a-zA-Zа-яА-ЯёЁ_][a-zA-Zа-яА-ЯёЁ_0-9]*'
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
start = 'program'

precedence = (
    ('left', 'COMMA'),
    ('left', 'OR'),
    ('left', 'AND'),
    ('left', 'EE', 'NEQ', 'LT', 'GT', 'GTE', 'LTE', 'IS', 'IN'),
    ('left', 'PLUS', 'MINUS'),
    ('left', 'MULTIPLE', 'DIVIDE', 'MOD'),
    ('right', 'POW'),
    ('right', 'UMINUS', 'UPLUS'),
    ('nonassoc', 'EQ', 'op'),
    ('nonassoc', 'LPAREN', 'RPAREN', 'LBRACKET', 'RBRACKET', 'LBRACK', 'RBRACK'),
    ('nonassoc', 'FUNC', 'VAR', 'FOR', 'RETURN', 'IF', 'OTHERWISE', 'ELSE', 'WHILE'),
)

def p_program(p):
    'program : statements'
    p[0] = ('program', p[1])

def p_statements_multiple(p):
    'statements : statements expression'
    p[0] = p[1] + [p[2]]

def p_statements_single(p):
    'statements : expression'
    p[0] = [p[1]]

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

def p_elements_empty(p):
    'elements :'
    p[0] = []

def p_bool(p):
    '''BOOL : TRUE
            | FALSE'''
    p[0] = p[1]

def p_element(p):
    '''element : NUMBER
               | STRING
               | BOOL
               | expression'''
    p[0] = p[1]

def p_factor_mod_var(p):
    'factor : ID DOT ID'
    modul, _ = p[1]
    var, _ = p[3]
    p[0] = ('modvar', modul, var)

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

def p_factor_bool(p):
    'factor : BOOL'
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

def p_expression_continue(p):
    'expression : CONTINUE'
    p[0] = ('continue',)

def p_expression_break(p):
    'expression : BREAK'
    p[0] = ('break',)

def p_expression_pass(p):
    'expression : PASS'
    p[0] = ('pass',)
    
def p_cond_mul(p):
    '''cond : LPAREN cond AND cond RPAREN
    | LPAREN cond OR cond RPAREN'''
    p[0] = (p[3], p[2], p[4])

def p_cond_logic(p):
    '''cond : expression logic expression
            | expression'''
    if len(p) == 4:
        p[0] = ('cond', p[1], p[2], p[3])
    else:
        p[0] = p[1]

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
    
def p_expression_logic(p):
    '''expression : expression AND expression
                  | expression OR expression'''
    p[0] = (p[2], p[1], p[3])

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
    if 'curmod' in globals():
        mod_funcs.setdefault(curmod, {})[name] = (params, body)
        symbol_table[name] = 'function'
    else:
        funcs[name] = (params, body)
        symbol_table[name] = 'function'
    p[0] = ('ownfunc', name, params, body)

def p_factor_mod_func(p):
    'factor : ID DOT ID LPAREN arguments RPAREN'
    modul, _ = p[1]
    func, _ = p[3]
    args = p[5]
    p[0] = ('modfunc', modul, func, args)

def p_factor_mod_func_noargs(p):
    'factor : ID DOT ID LPAREN RPAREN'
    modul, _ = p[1]
    func, _ = p[3]
    p[0] = ('modfunc', modul, func, [])

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
    
def p_expression_plain_assign(p):
    'expression : ID EQ expression'
    name, _ = p[1]
    val = p[3]
    p[0] = ('assignpl', name, val)

def p_expression_newAssign(p):
    '''expression : ID op expression'''
    name, _ = p[1]
    opera = p[2]
    val = p[3]
    p[0] = ('newAssign', name, val, opera)
    
def p_array_index(p):
    '''expression : ID LBRACK expression RBRACK'''
    
    p[0] = ('arrindx', p[1], p[3])

def p_error(p):
    if p:
        print(f"Syntax error at token '{p.value}' (type: {p.type}) on line {p.lineno}")
        while p and p.type not in ('\n', 'RBRACKET', 'SEMI'):
            lexer.skip(1)
            p = lexer.token()
    else:
        print("Syntax error at EOF")

parser = yacc.yacc()

# === Interpreter ===
def eval_ast(node, localVarsCache=None):
    global vars, mod_vars, mod_funcs, curmod, vars_stack
    if localVarsCache is None:
        localVarsCache = {}
    if isinstance(node, str) and node in ('true', 'false'):
        return node == 'true'
    if isinstance(node, (int, float, str, list, bool)):
        return node
    if node[0] == 'number':
        return node[1]
    if node[0] == 'string':
        return node[1]
    if node[0] == 'id':
        if node[1] in localVarsCache:
            return localVarsCache[node[1]]
        if node[1] in vars:
            return vars[node[1]]
        raise NameError(f"Variable '{node[1]}' not defined")
    if node[0] == 'program':
        result = None
        for stmt in node[1]:
            result = eval_ast(stmt)
        return result
    if node[0] == 'error':
        raise NameError(f"'{node[1]}' is not a function")
    if node[0] == 'neg':
        return -eval_ast(node[1])
    if node[0] == 'import':
        modul = node[1]
        mod_vars[modul] = {}
        mod_funcs[modul] = {}
        curmod = modul
        try:
            with open(modul + '.nmod', 'r', encoding='utf-8') as f:
                code = f.read()
            parsed = parser.parse(code)
            if parsed:
                vars_stack.append(vars.copy())
                vars.clear()
                vars.update(mod_vars[modul])
                eval_ast(parsed)
                mod_vars[modul] = vars.copy()
                vars.clear()
                vars.update(vars_stack.pop())
            del curmod
        except FileNotFoundError:
            print(f"Module '{modul}' not found")
        return None
    if node[0] == 'modvar':
        modul, var = node[1], node[2]
        if modul in mod_vars and var in mod_vars[modul]:
            return mod_vars[modul][var]
        raise NameError(f"Variable '{var}' not found in module '{modul}'")
    if node[0] == 'modfunc':
        modul, func, args = node[1], node[2], node[3]
        args = [eval_ast(arg) for arg in args]
        if modul in mod_funcs and func in mod_funcs[modul]:
            arg_names, body = mod_funcs[modul][func]
            vars_stack.append(vars.copy())
            vars.clear()
            vars.update(mod_vars[modul])
            for i in range(min(len(arg_names), len(args))):
                vars[arg_names[i]] = args[i]
            old_cur = globals().get('curmod')
            globals()['curmod'] = modul
            result = eval_ast(body)
            vars.clear()
            vars.update(vars_stack.pop())
            if old_cur is not None:
                globals()['curmod'] = old_cur
            else:
                del globals()['curmod']
                
            return result
        raise NameError(f"Function '{func}' not found in module '{modul}'")
    if node[0] == 'array':
        els = node[1]
        return [eval_ast(el) for el in els]
    if node[0] == 'block':
        _, statements = node
        if len(statements) == 1:
            return eval_ast(statements[0])
        result = None
        for stmt in statements:
            result = eval_ast(stmt)
            if isinstance(result, tuple) and result[0] in ('return', 'continue', 'break'):
                return result
        return result
    if node[0] == 'return':
        return eval_ast(node[1])
    if node[0] == 'continue':
        return ('continue',)
    if node[0] == 'break':
        return ('break',)
    if node[0] == 'pass':
        return None
    if node[0] == 'alwaysDo':
        body = node[1]
        result = None
        while True:
            block_result = eval_ast(body)
            if isinstance(block_result, tuple):
                if block_result[0] == 'return':
                    return block_result
                if block_result[0] == 'break':
                    break
                if block_result[0] == 'continue':
                    continue
            result = block_result
        return result
    if node[0] == 'ternar':
        cond = node[1]
        body = node[2]
        elsebody = node[3]
        cond1 = eval_ast(cond)
        return eval_ast(body if cond1 else elsebody)
    if node[0] == 'ifExp':
        cond = node[1]
        body1 = node[2]
        body2 = node[3]
        cond1 = eval_ast(cond)
        return eval_ast(body1 if cond1 else body2) if body2 else eval_ast(body1) if cond1 else None
    if node[0] == 'while':
        cond = node[1]
        body = node[2]
        result = None
        while True:
            cond1 = eval_ast(cond)
            if not cond1:
                break
            block_result = eval_ast(body)
            if isinstance(block_result, tuple):
                if block_result[0] == 'return':
                    return block_result
                if block_result[0] == 'break':
                    break
                if block_result[0] == 'continue':
                    continue
            result = block_result
        return result
    if node[0] == 'for':
        _, var, start, end, body = node
        start_val = eval_ast(start)
        end_val = eval_ast(end)
        if not isinstance(start_val, (int, float)) or not isinstance(end_val, (int, float)):
            raise ValueError("For loop start and end must be numbers")
        oldval_ = vars.get(var)
        result = None
        step = 1 if start_val <= end_val else -1
        if body[0] == 'block' and len(body[1]) == 1 and body[1][0][0] == 'call' and body[1][0][1] == 'output' and len(body[1][0][2]) == 1 and body[1][0][2][0][0] == 'id' and body[1][0][2][0][1] == var:
            for i in range(int(start_val), int(end_val) + (1 if step > 0 else -1), step):
                print(i)
            return None
        for i in range(int(start_val), int(end_val) + (1 if step > 0 else -1), step):
            vars[var] = i
            localVarsCache = {var: i}
            block_result = eval_ast(body, localVarsCache)
            if isinstance(block_result, tuple):
                if block_result[0] == 'return':
                    if oldval_ is None:
                        vars.pop(var, None)
                    else:
                        vars[var] = oldval_
                    return block_result
                if block_result[0] == 'break':
                    break
                if block_result[0] == 'continue':
                    continue
            result = block_result
        if oldval_ is None:
            vars.pop(var, None)
        else:
            vars[var] = oldval_
        return result
    if node[0] == 'assign':
        _, name, expr = node
        val = eval_ast(expr)
        vars[name] = val
        return val
    if node[0] == 'assignpl':
        name, expr = node[1], node[2]
        val = eval_ast(expr)
        if name not in vars:
            raise NameError(f"Variable '{name}' is not defined")
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
    if node[0] == '&&':
        left = eval_ast(node[1])
        if not left:
            return False
        return eval_ast(node[2])
    if node[0] == '||':
        left = eval_ast(node[1])
        if left:
            return True
        return eval_ast(node[2])
    if node[0] == 'cond':
        left = eval_ast(node[1])
        op = node[2]
        right = eval_ast(node[3])
        if op == 'partof' and isinstance(right, (int, float)):
            right = [right]
        if op == '==':
            return left == right
        elif op == '!==':
            return left != right
        elif op == '<':
            return left < right
        elif op == '>':
            return left > right
        elif op == '>=':
            return left >= right
        elif op == '<=':
            return left <= right
        elif op == 'is':
            return left is right
        elif op == 'partof':
            if not isinstance(right, (list, str, tuple)):
                raise ValueError(f"Operator 'partof' expects an iterable as right operand, got {type(right).name}")
            return left in right
        else:
            raise ValueError(f"Unknown operator in cond: {op}")
    if node[0] == 'call':
        name, ar = node[1], node[2]
        args = []
        for a in ar:
            if a[0] == 'id':
                value = vars.get(a[1])
                if value is None:
                    raise NameError(f"Variable '{a[1]}' is not defined")
                args.append(value)
            else:
                args.append(eval_ast(a)) 
        if name == 'output' and len(args) == 1:
            arg = args[0]
            if isinstance(arg, (int, float, str, bool)):
                print(arg)
                return None
            if arg[0] in ('id', 'number'):
                value = arg[1] if arg[0] == 'number' else localVarsCache(arg[1], vars[arg[1]])
                print(value)
                return None
        if name == 'output':
            print(*[str(arg) if isinstance(arg, list) else arg for arg in args], file=sys.stderr, flush=True)
            return None
        if name == 'input':
            prompt = args[0] if len(args) != 0 else None
            if prompt is not None:
                user_input = input(args[0])
            else:
                user_input = input()
            try:
                return int(user_input)
            except ValueError:
                return user_input
        if name == 'charCodeAt':
            char = args[0]
            return ord(char)
        if name == 'charCodeFrom':
            return chr(args[0])
        if name == 'substring':
            string = args[0]
            start = args[1]
            end = args[2]
            if isinstance(start, tuple):
                start = eval_ast(start)
                start = int(start)
            if isinstance(end, tuple):
                end = eval_ast(end)
                end = int(end)
            int(start)
            int(end)
            return string[start:end]
        if name == 'split':
            string = args[0]
            delimiter = args[1]
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
        if name == 'replace':
            old = args[0]
            new = args[1]
            string = args[2]
            return string.replace(old, new)
        if name == 'sort':
            arr = args[0]
            if not isinstance(arr, list):
                raise ValueError(f"Variable '{arr}' is not an array")
            arr.sort()
            return arr
        if name =='reverse':
            arr = args[0]
            if not isinstance(arr, list):
                raise ValueError(f"Variable '{arr}' is not an array")
            arr.reverse()
            return arr
        if name == 'exit':
            exit()
        if name == 'typeof':
            if isinstance(args[0], str):
                return 'string'
            if isinstance(args[0], int):
                return 'int'
            if isinstance(args[0], float):
                return 'float'
            if isinstance(args[0], list):
                return 'array'
            if args[0] is None:
                return 'null'
            if isinstance(args[0], bool):
                return 'bool'
            if args[0] == 'function':
                return 'function'
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
                raise ValueError(f"Variable '{arr}' is not an array")
            arr.append(el)
            return arr
        if name == 'pop':
            arr = args[0]
            el = args[1]
            if not isinstance(arr, list):
                raise ValueError(f"Variable '{arr}' is not an array")
            return arr.pop(el)
        if name == 'push':
            arr, el = args
            if not isinstance(arr, list):
                raise ValueError(f"Variable '{arr}' is not an array")
            arr.push(el)
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
            res = args[0] * (math.e ** args[0])
            return res
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
        if 'curmod' in globals() and curmod in mod_funcs and name in mod_funcs[curmod]:
            arg_names, body = mod_funcs[curmod][name]
            old_vars = vars.copy()
            for i in range(min(len(arg_names), len(args))):
                vars[arg_names[i]] = args[i]
            result = eval_ast(body)
            vars.clear()
            vars.update(old_vars)
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
    if isinstance(node, tuple) and len(node) == 2 and isinstance(node[1], str):
        name, _ = node
        if name in vars:
            return vars[name]
        raise NameError(f"Variable '{name}' is not defined")
    if node[0] == 'arrindx':
        name, _ = node[1]
        indx = node[2]
        if isinstance(indx, tuple):
            indx = eval_ast(indx)
            indx = int(indx)
        else:
            indx = int(indx)
            
        if indx < 0 or indx >= len(vars[name]):
            raise IndexError(f"Index '{indx}' is out of range")
            
        if isinstance(vars[name], list):
            return vars[name][indx]
        elif isinstance(vars[name], str):
            return vars[name][indx]
        
        raise NameError(f"Variable '{name}' is not defined or it not list")
    if isinstance(node, tuple) and len(node) == 3:
        op, left, right = node
        left_val = eval_ast(left)
        right_val = eval_ast(right)
        if op == '+': return left_val + right_val
        if op == '-': return left_val - right_val
        if op == '*': return left_val * right_val
        if op == '/': return left_val / right_val
        if op == '^': return left_val ** right_val
        if op == '%': return left_val % right_val
    raise ValueError(f"Unknown node: {node}")

# === Test Run ===
while True:
    code = input("Enter your code: ")
    if code.startswith("run "):
        filename = code[4:].strip()
        with open(filename, "r", encoding='utf-8') as f:
            code = f.read()
    result = parser.parse(code)
    if result is None:
        print("Parsing failed due to syntax error")
    else:
        eval_ast(result)