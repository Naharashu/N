import ply.lex as lex
import ply.yacc as yacc
import math
import random
import sys
import hashlib

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

def symbol_lookup(identifier):
    return symbol_table.get(identifier, 'unknown')

# === Lexer ===
tokens = (
    'NUMBER', 'STRING', 'TRUE', 'FALSE', 'VAR', 'CONST', 'FOR', 'FUNC', 'RETURN', 'IF', 'OTHERWISE', 'WHILE', 'ELSE', 'FOREACH', 'ID',
    'PLUS', 'MINUS', 'MULTIPLE', 'DIVIDE', 'POW', 'MOD', 'DOT',
    'LPAREN', 'RPAREN', 'LBRACKET', 'LBRACK', 'RBRACK', 'RBRACKET',
    'COMMA', 'EQ', 'EE', 'NEQ', 'LT', 'GT', 'GTE', 'LTE', 'op', 'IS', 'IN', 'DO', 'ALWAYS', 'TWODOTS', 'QUE', 'IMPORT', 'SEMI',
    'CONTINUE', 'BREAK', 'PASS', 'AND', 'OR', 'NULL', 'TRY', 'CATCH', 'RAISE', 'YIELD', 'DEFINE', 'LAMBDA'
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
    r'\+\=|-\=|\*\=|\/\=|\^\=|\>\>|\<\<'
    return t

def t_DEFINE(t):
    r'define'
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

def t_TRY(t):
    r'try'
    return t

def t_CATCH(t):
    r'catch'
    return t

def t_RAISE(t):
    r'raise'
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

def t_CONST(t):
    r'const'
    return t

def t_YIELD(t):
    r'yield'
    return t

def t_FOREACH(t):
    r'foreach'
    return t

def t_FOR(t):
    r'for'
    return t
    
def t_LAMBDA(t):
	r'lambda'
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
    ('nonassoc', 'FUNC', 'VAR', 'FOR', 'RETURN', 'IF', 'OTHERWISE', 'ELSE', 'WHILE', 'FOREACH'),
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
    p[0] = ('number', p[1])

def p_factor_string(p):
    'factor : STRING'
    p[0] = ('string', p[1])

def p_factor_bool(p):
    'factor : BOOL'
    p[0] = p[1]

def p_factor_id(p):
    'factor : ID'
    p[0] = ('id', p[1])

def p_factor_array(p):
    'factor : array'
    p[0] = p[1]

def p_factor_null(p):
    'factor : NULL'
    p[0] = ('null',)

def p_expression_def(p):
    'expression : DEFINE ID LPAREN params RPAREN block'
    name, _ = p[2]
    params = p[4]
    body = p[6]
    funcs[name] = ('define', params, body)
    symbol_table[name] = 'define'
    p[0] = ('define', name, params, body)

def p_expression_return(p):
    'expression : RETURN retval'
    p[0] = ('return', p[2])

def p_retval_multiple(p):
    'retval : LPAREN retval COMMA expression RPAREN'
    p[0] = p[1] + [p[3]]

def p_retval_single(p):
    'retval : expression'
    p[0] = p[1]
    
def p_expression_lambda(p):
	'expression : LAMBDA LPAREN params RPAREN block'
	p[0] = ('lambda', p[3], p[5])
	
def p_factor_lambda_call(p):
    'factor : LPAREN expression RPAREN LPAREN arguments RPAREN'
    p[0] = ('call', p[2], p[5])
def p_factor_lambda_call_noargs(p):
    'factor : LPAREN expression RPAREN LPAREN RPAREN'
    p[0] = ('call', p[2], [])

def p_yield(p):
    'expression : YIELD expression'
    p[0] = ('yield', p[2])

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

def p_try_catch(p):
    'expression : TRY block CATCH LPAREN ID RPAREN block'
    p[0] = ('try_catch', p[2], p[5], p[7])

def p_expression_while(p):
    'expression : WHILE cond block'
    cond = p[2]
    body = p[3]
    p[0] = ('while', cond, body)

def p_expression_alwaysdo(p):
    'expression : ALWAYS DO block'
    body = p[3]
    p[0] = ('alwaysDo', body)

def p_expression_raise(p):
    'expression : RAISE expression'
    p[0] = ('raise', p[2])

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
        p[0] = ('call', name, args)  # Буде перевірено в інтерпретаторі

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
    
def p_dict(p):
    'dict : LBRACKET dict_pairs RBRACKET'
    p[0] = ('dict', p[2])

def p_dict_pairs_multiple(p):
    'dict_pairs : dict_pairs COMMA dict_pair'
    p[0] = p[1] + [p[3]]

def p_dict_pairs_single(p):
    'dict_pairs : dict_pair'
    p[0] = [p[1]]

def p_dict_pairs_empty(p):
    'dict_pairs :'
    p[0] = []

def p_dict_pair(p):
    'dict_pair : STRING TWODOTS element'
    p[0] = (p[1], p[3])

def p_factor_dict(p):
    'factor : dict'
    p[0] = p[1]

def p_expression_for(p):
    'expression : FOR LPAREN ID COMMA expression COMMA expression RPAREN block'
    name, _ = p[3]
    p[0] = ('for', name, p[5], p[7], p[9])

def p_expression_foreach(p):
    'expression : FOREACH LPAREN ID IN expression RPAREN block'
    name, _ = p[3]
    iterable = p[5]
    body = p[7]
    p[0] = ('foreach', name, iterable, body)

def p_expression_assign(p):
    '''expression : VAR ID EQ expression
                  | CONST ID EQ expression'''
    type = p[1]
    name, _ = p[2]
    val = p[4]
    p[0] = ('assign', type, name, val)

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
def replace_params(node, replacements):
    if isinstance(node, list):
        return [replace_params(child, replacements) for child in node]
    if not isinstance(node, tuple):
        return node
    if node[0] == 'id' and isinstance(node[1], tuple) and node[1][0] in replacements:
        return replacements[node[1][0]]
    return tuple(
        replace_params(child, replacements) if isinstance(child, (tuple, list)) else child
        for child in node
    )

def eval_ast(node, localVarsCache=None):
    global scope_stack, vars, consts, mod_vars, mod_funcs, vars_stack, funcs
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
        var_name = node[1][0] if isinstance(node[1], tuple) else node[1]
        if var_name in localVarsCache:
            return localVarsCache[var_name]
        return find_variable(var_name)
    if node[0] == 'name':
        return node[1]
    if node[0] == 'dict':
        pairs = node[1]
        result = {}
        for key, value in pairs:
            result[key] = eval_ast(value)
        return result
    if node[0] == 'program':
        result = None
        for stmt in node[1]:
            result = eval_ast(stmt, localVarsCache)
        return result
    if node[0] == 'define':
        name, params, body = node[1], node[2], node[3]
        funcs[name] = ('define', params, body)
        return None
    if node[0] == 'error':
        raise NameError(f"'{node[1]}' is not a function")
    if node[0] == 'neg':
        return -eval_ast(node[1])
    if node[0] == 'null':
        return None
    if node[0] == 'import':
        modul = node[1]
        mod_vars[modul] = {}
        mod_funcs[modul] = {}
        try:
            with open(modul + '.nmod', 'r', encoding='utf-8') as f:
                code = f.read()
            parsed = parser.parse(code)
            if parsed:
                enter_scope()
                vars_stack.append(scope_stack[-1].copy())
                scope_stack[-1].update(mod_vars[modul])
                globals()['curmod'] = modul
                eval_ast(parsed)
                mod_vars[modul] = scope_stack[-1].copy()
                mod_funcs[modul] = {k: v for k, v in scope_stack[-1].items() if isinstance(v, tuple) and v[0] == 'func'}
                exit_scope()
                scope_stack[-1] = vars_stack.pop()
                del globals()['curmod']
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
            arg_names, body = mod_funcs[modul][func][1], mod_funcs[modul][func][2]
            enter_scope()
            for i in range(min(len(arg_names), len(args))):
                update_variable(arg_names[i], args[i])
            globals()['curmod'] = modul
            result = eval_ast(body)
            exit_scope()
            del globals()['curmod']
            return result
        raise NameError(f"Function '{func}' not found in module '{modul}'")
    if node[0] == 'array':
        els = node[1]
        return [eval_ast(el) for el in els]
    if node[0] == 'block':
        enter_scope()
        result = None
        for stmt in node[1]:
            result = eval_ast(stmt, localVarsCache)
            if isinstance(result, tuple) and result[0] in ('return', 'continue', 'break'):
                exit_scope()
                return result
        exit_scope()
        return result
    if node[0] == 'return':
        return ('return', eval_ast(node[1], localVarsCache))
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
            enter_scope()
            block_result = eval_ast(body)
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
    if node[0] == 'ternar':
        cond = node[1]
        body = node[2]
        elsebody = node[3]
        cond1 = eval_ast(cond)
        return eval_ast(body if cond1 else elsebody)
    if node[0] == 'try_catch':
        try:
            return eval_ast(node[1], localVarsCache)
        except Exception as e:
            enter_scope()
            update_variable(node[2][0], str(e))
            result = eval_ast(node[3], localVarsCache)
            exit_scope()
            return result
    if node[0] == 'raise':
        value = eval_ast(node[1])
        raise Exception(value)
    if node[0] == 'ifExp':
        cond = node[1]
        body1 = node[2]
        body2 = node[3]
        cond1 = eval_ast(cond)
        enter_scope()
        result = eval_ast(body1 if cond1 else body2) if body2 else (eval_ast(body1) if cond1 else None)
        exit_scope()
        return result
    if node[0] == 'while':
        cond = node[1]
        body = node[2]
        result = None
        while True:
            cond1 = eval_ast(cond)
            if not cond1:
                break
            enter_scope()
            block_result = eval_ast(body)
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
    if node[0] == 'foreach':
        name = node[1]
        iterable = eval_ast(node[2])
        body = node[3]
        result = None
        if not isinstance(iterable, (list, str)):
            raise ValueError(f"Expected an iterable in foreach, got {type(iterable).__name__}")
        for item in iterable:
            enter_scope()
            update_variable(name, item)
            block_result = eval_ast(body, localVarsCache)
            exit_scope()
            if isinstance(block_result, tuple) and block_result[0] in ('break', 'return', 'continue'):
                if block_result[0] == 'break':
                    break
                if block_result[0] == 'continue':
                    continue
                return block_result
            result = block_result
        return result
    if node[0] == 'for':
        _, var, start, end, body = node
        start_val = eval_ast(start)
        end_val = eval_ast(end)
        if not isinstance(start_val, (int, float)) or not isinstance(end_val, (int, float)):
            raise ValueError("For loop start and end must be numbers")
        enter_scope()
        update_variable(var, start_val)
        result = None
        step = 1 if start_val <= end_val else -1
        for i in range(int(start_val), int(end_val) + (1 if step > 0 else -1), step):
            update_variable(var, i)
            block_result = eval_ast(body, localVarsCache)
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
    if node[0] == 'assign':
        _, type, name, expr = node
        val = eval_ast(expr)
        is_const = type == 'const'
        update_variable(name, val, is_const)
        return val
    if node[0] == 'assignpl':
        name, expr = node[1], node[2]
        val = eval_ast(expr)
        update_variable(name, val)
        return val
    if node[0] == 'newAssign':
        name = node[1]
        val = eval_ast(node[2])
        opera = node[3]
        res = find_variable(name)
        if name in consts:
            raise ValueError(f"Cannot reassign constant '{name}'")
        if opera == '+=':
            res += val
        elif opera == '-=':
            res -= val
        elif opera == '*=':
            res *= val
        elif opera == '/=':
            res /= val
        elif opera == '^=':
            res **= val
        elif opera == '>>':
            res >>= val
        elif opera == '<<':
            res <<= val
        else:
            raise NameError(f"Operation '{opera}' is not allowed")
        update_variable(name, res)
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
                raise ValueError(f"Operator 'partof' expects an iterable, got {type(right).__name__}")
            return left in right
        else:
            raise ValueError(f"Unknown operator in cond: {op}")
    if node[0] == 'call':
        name, ar = node[1], node[2]
        if name in funcs:
            if funcs[name][0] == 'define':
                _, args_names, body = funcs[name]
                args = [eval_ast(a, localVarsCache) for a in ar]
                replacements = {}
                for arg_name, arg_value in zip(args_names, args):
                    replacements[arg_name] = arg_value
                new_body = replace_params(body, replacements)
                enter_scope()
                result = eval_ast(new_body, localVarsCache)
                exit_scope()
                
                if isinstance(result, tuple) and result[0] == 'return':
                    return result[1]
                return result
        args = [eval_ast(a, localVarsCache) for a in ar]
        if name == 'output':
            print(*[str(arg) if isinstance(arg, list) else arg for arg in args])
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
            if not isinstance(string, str):
                raise ValueError(f"Expected a string for substring, got {type(string).__name__}")
            if not isinstance(start, (int, float)) or not isinstance(end, (int, float)):
                raise ValueError("Start and end indices must be numbers")
            start, end = int(start), int(end)
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
        if name == 'sha1':
            return hashlib.sha1(args[0].encode()).hexdigest()
        if name == 'sha256':
            return hashlib.sha256(args[0].encode()).hexdigest()
        if name == 'replace':
            old = args[0]
            new = args[1]
            string = args[2]
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
            arr, el = args[0], args[1]
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
            res = args[0] * (math.e ** args[0])
            return res
        if name == 'factorial':
            res = args[0]
            return math.factorial(res)
        if 'curmod' in globals() and modul in mod_funcs and name in mod_funcs[modul]:
            arg_names, body = mod_funcs[modul][name][1], mod_funcs[modul][name][2]
            enter_scope()
            for i in range(min(len(arg_names), len(args))):
                update_variable(arg_names[i], args[i])
            result = eval_ast(body)
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
        for i, param in enumerate(params):
            update_variable(param, args[i])
        result = eval_ast(body)
        exit_scope()
        return result[1] if isinstance(result, tuple) and result[0] == 'return' else result
    if node[0] == 'ownfunc':
        name, params, body = node[1], node[2], node[3]
        update_variable(name, ('func', params, body))
        symbol_table[name] = 'function'
        return None
    if node[0] == 'lambda':
        params, body = node[1], node[2]
        return ('func', params, body)
    if node[0] == 'arrindx':
        name, _ = node[1]
        indx = eval_ast(node[2])
        arr = find_variable(name)
        if not isinstance(arr, (list, str, dict)):
            raise TypeError(f"Variable '{name}' is not indexable")
        if isinstance(arr, dict):
            if indx not in arr:
                raise KeyError(f'key {indx} not found in dict')
            return arr[indx]
        if not isinstance(indx, (int, float)) or indx < 0 or indx >= len(arr):
            raise IndexError(f"Index {indx} out of range")
        return arr[int(indx)]
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
    try:
        code = input("Enter your code: ")
        lines = code.split('\n')
        if code.startswith("run "):
            filename = code[4:].strip()
            with open(filename, "r", encoding='utf-8') as f:
                code = f.read()
                lines = code.split('\n')
        result = parser.parse(code)
        if result is None:
            print("Parsing failed due to syntax error")
        else:
            eval_ast(result)
    except KeyboardInterrupt:
        print("\nExiting...")
        break
    except Exception as e:
        print(f"Error: {e}")
