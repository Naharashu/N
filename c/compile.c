#include "compile.h"
#include "scanner.h"
#include "common.h"
#include "object.h"
#ifdef DEBUG_PRINT_CODE
#include "debug.h"
#endif
#include <stdlib.h>
#include <string.h>

typedef struct 
{
    Token current;
    Token previous;
    bool hadError;
    bool panicMode;
} Parser;

typedef enum {
    PREC_NONE,
    PREC_ASSIGNMENT,
    PREC_OR, 
    PREC_AND,
    PREC_EQUALITY,
    PREC_COMPARISON,
    PREC_TERM,
    PREC_FACTOR,
    PREC_UNARY,
    PREC_CALL,
    PREC_PRIMARY
} Precedence;

typedef void(*ParserFn)(bool canAssign);

typedef struct {
    ParserFn prefix;
    ParserFn infix;
    Precedence precedence;
} ParseRule;

typedef struct {
    Token name;
    int depth;
    bool isConst;
} Local;

typedef struct {
    Local locals[UINT16_COUNT];
    int localCount;
    int scopeDepth;
} Compiler;

Parser parser;
Compiler* current = NULL;
Chunk* compilingChunk;

static void grouping(bool canAssign);
static void unary(bool canAssign);
static void binary(bool canAssign);
static void number(bool canAssign);
static void literal(bool canAssign);
static void string(bool canAssign);
static void statement();
static void declaration();
static void variable(bool canAssign);
static void constVar(bool canAssign);
static void and_(bool canAssign);
static void or_(bool canAssign);
static void inputStatement(bool canAssign);


ParseRule rules[] = {
  [TOKEN_LEFT_PAREN]    = {grouping, NULL,   PREC_NONE},
  [TOKEN_RIGHT_PAREN]   = {NULL,     NULL,   PREC_NONE},
  [TOKEN_LEFT_BRACE]    = {NULL,     NULL,   PREC_NONE}, 
  [TOKEN_RIGHT_BRACE]   = {NULL,     NULL,   PREC_NONE},
  [TOKEN_COMMA]         = {NULL,     NULL,   PREC_NONE},
  [TOKEN_DOT]           = {NULL,     NULL,   PREC_NONE},
  [TOKEN_MINUS]         = {unary,    binary, PREC_TERM},
  [TOKEN_PLUS]          = {NULL,     binary, PREC_TERM},
  [TOKEN_SEMICOLON]     = {NULL,     NULL,   PREC_NONE},
  [TOKEN_SLASH]         = {NULL,     binary, PREC_FACTOR},
  [TOKEN_STAR]          = {NULL,     binary, PREC_FACTOR},
  [TOKEN_POW]           = {NULL,     binary, PREC_FACTOR},
  [TOKEN_BANG]          = {unary,     NULL,   PREC_NONE},
  [TOKEN_BANG_EQUAL]    = {NULL,     binary,   PREC_EQUALITY},
  [TOKEN_EQUAL]         = {NULL,     NULL,   PREC_NONE},
  [TOKEN_EQUAL_EQUAL]   = {NULL,     binary,   PREC_EQUALITY},
  [TOKEN_GREATER]       = {NULL,     binary,   PREC_COMPARISON},
  [TOKEN_GREATER_EQUAL] = {NULL,     binary,   PREC_COMPARISON},
  [TOKEN_LESS]          = {NULL,     binary,   PREC_COMPARISON},
  [TOKEN_LESS_EQUAL]    = {NULL,     binary,   PREC_COMPARISON},
  [TOKEN_IDENTIFIER]    = {variable,     NULL,   PREC_NONE},
  [TOKEN_STRING]        = {string,     NULL,   PREC_NONE},
  [TOKEN_NUMBER]        = {number,   NULL,   PREC_NONE},
  [TOKEN_AND]           = {NULL,     and_,   PREC_AND},
  [TOKEN_CLASS]         = {NULL,     NULL,   PREC_NONE},
  [TOKEN_ELSE]          = {NULL,     NULL,   PREC_NONE},
  [TOKEN_FALSE]         = {literal,  NULL,   PREC_NONE},
  [TOKEN_FOR]           = {literal,     NULL,   PREC_NONE},
  [TOKEN_FUN]           = {NULL,     NULL,   PREC_NONE},
  [TOKEN_IF]            = {NULL,     NULL,   PREC_NONE},
  [TOKEN_NIL]           = {literal,     NULL,   PREC_NONE},
  [TOKEN_OR]            = {NULL,     or_,   PREC_OR},
  [TOKEN_PRINT]         = {NULL,     NULL,   PREC_NONE},
  [TOKEN_INPUT]         = {inputStatement,     NULL,   PREC_NONE},
  [TOKEN_RETURN]        = {NULL,     NULL,   PREC_NONE},
  [TOKEN_SUPER]         = {NULL,     NULL,   PREC_NONE},
  [TOKEN_THIS]          = {NULL,     NULL,   PREC_NONE},
  [TOKEN_TRUE]          = {literal,     NULL,   PREC_NONE},
  [TOKEN_VAR]           = {NULL,     NULL,   PREC_NONE},
  [TOKEN_CONST]         = {NULL,     NULL,   PREC_NONE},
  [TOKEN_WHILE]         = {NULL,     NULL,   PREC_NONE},
  [TOKEN_ERROR]         = {NULL,     NULL,   PREC_NONE},
  [TOKEN_EOF]           = {NULL,     NULL,   PREC_NONE},
};

static ParseRule* getRule(TokenType type) {
    return &rules[type]; 
}

static Chunk* currentChunk() {
   return compilingChunk;
}



static void errorAt(Token* token, const char* message) {
    if(parser.panicMode) return;
    parser.panicMode = true;
    fprintf(stderr, "[line %d] Error", token->line);

    if (token->type == TOKEN_EOF) {
        fprintf(stderr, " at end");
    } else if (token->type == TOKEN_ERROR) {
        
    } else {
        fprintf(stderr, " at '%.*s'", token->length, token->start);
    }

    fprintf(stderr, ": %s\n", message);
    parser.hadError = true;
}

static void error(const char* message) {
    errorAt(&parser.previous, message);
}

static void errorAtCurrent(const char* message) {
    errorAt(&parser.current, message);
}


static void advance() {
    parser.previous = parser.current;
    for(;;) {
        parser.current = scanToken();
        if(parser.current.type != TOKEN_ERROR) break;
        errorAtCurrent(parser.current.start);
    }
}

static void consume(TokenType type, const char* message) {
    if (parser.current.type == type) {
        advance();
        return;
    }

    errorAtCurrent(message);
}

static bool check(TokenType type) {
    return parser.current.type == type;
}

static bool match(TokenType type) {
    if (!check(type)) return false;
    advance();
    return true;
}

static void emitByte(uint8_t byte) {
   writeChunk(currentChunk(), byte, parser.previous.line); 
}

static void emitBytes(uint8_t byte1, uint8_t byte2) {
    emitByte(byte1);
    emitByte(byte2);
}

static void emitReturn() {
    emitByte(OP_RETURN);
}

static uint16_t makeConstant(Value value) {
    int constant = addConstant(currentChunk(), value);
    if (constant > UINT16_MAX) {
        error("Too many constants in one chunk.");
        return 0;
    }
    return (uint16_t)constant;
}

static void emitConstant(Value value) {
    uint16_t constant = makeConstant(value);
    emitByte(OP_CONSTANT);
    emitByte((constant >> 8) & 0xff);
    emitByte(constant & 0xff);
}

static void patchJump(int offset) {
    int jump = currentChunk()->count - offset - 2;
    if(jump > (UINT16_MAX)) {
        error("Too far jump.");
    }
    currentChunk()->code[offset]  = (jump >> 8) & 0xff;
    currentChunk()->code[offset+1] = jump & 0xff;
}

static int emitJump(uint8_t instruction) {
    emitByte(instruction);
    emitByte(0xff);
    emitByte(0xff);
    return currentChunk()->count - 2;    
}

static void initCompiler(Compiler* compiler) {
    compiler->localCount = 0;
    compiler->scopeDepth = 0;
    current = compiler;
}

static void emitLoop(int loopStart) {
    emitByte(OP_LOOP);

    int offset = currentChunk()->count - loopStart - 2;
    if(offset > (UINT16_MAX)) {
        error("InterpreteError: Too far jump(while).");
    }
    emitByte((offset >> 8) & 0xff);
    emitByte(offset & 0xff);
}

static void parsePrecedence(Precedence precedence) {
   advance();
   ParserFn prefixRule = getRule(parser.previous.type)->prefix;
   if(prefixRule == NULL) {
       error("Expect expression.");
       return;
   }

   bool canAssign = precedence <= PREC_ASSIGNMENT;
   prefixRule(canAssign);
   while(precedence <= getRule(parser.current.type)->precedence) {
       advance();
       ParserFn infixRule = getRule(parser.previous.type)->infix;
       infixRule(canAssign) ;
   }
   if(canAssign && match(TOKEN_EQUAL)) {
       error("Invalid assignment target."); 
   }
}

static uint16_t identifierConstant(Token* name) {
    return makeConstant(OBJ_VAL(copyString(name->start, name->length)));
}

static bool identifiersEqual(Token* a, Token* b) {
    if(a->length != b->length) return false;
    return memcmp(a->start, b->start, a->length) == 0;
}

static void addLocal(Token name, bool isconst) {
    if (current->localCount == UINT16_MAX) {
        error("Too many local variables in function.");
        return;
    }
    for (int i = current->localCount - 1; i >= 0; i--) {
        Local* local = &current->locals[i];
        if (local->depth != -1 && local->depth < current->scopeDepth) {
            break; 
        }
        if (identifiersEqual(&name, &local->name)) {
            printf("Variable already declared in this scope on %d line.\n", name.line);
            error("");
            return;
        }
    }
    Local* local = &current->locals[current->localCount++];
    local->isConst = isconst;
    local->name = name;
    local->depth = -1; 
}

static void declareVariable(bool isconst) {
    if (current->scopeDepth == 0) return;
    Token* name = &parser.previous;
    addLocal(*name, isconst);
}

static uint16_t parseVariable(const char* message, bool isconst) {
    consume(TOKEN_IDENTIFIER, message);
    declareVariable(isconst);
    if (current->scopeDepth > 0) return 0;
    return identifierConstant(&parser.previous);
}

static void defineVariable(uint16_t global, bool isconst) {
    if (current->scopeDepth > 0) {
        current->locals[current->localCount - 1].depth = current->scopeDepth;
        current->locals[current->localCount - 1].isConst = isconst;
        return;
    }
    if (isconst) {
        emitByte(OP_DEFINE_GLOBAL_CONST);
    } else {
        emitByte(OP_DEFINE_GLOBAL);
    }
    emitByte((global >> 8) & 0xff);
    emitByte(global & 0xff);
}

static void expression() {
    parsePrecedence(PREC_ASSIGNMENT);
}

static void printStatement() {
    consume(TOKEN_LEFT_PAREN, "Expect '(' after 'print'.");
    consume(TOKEN_RIGHT_PAREN, "Expect ')' after expression.");
    consume(TOKEN_SEMICOLON, "Expect ';' after value.");
    emitByte(OP_PRINT);
}

static void inputStatement(bool canAssign) {
    consume(TOKEN_LEFT_PAREN, "Expect '(' after 'input'.");
    if (!check(TOKEN_RIGHT_PAREN)) {
        expression();
        emitByte(OP_POP); 
    }
    consume(TOKEN_RIGHT_PAREN, "Expect ')' after expression.");
    consume(TOKEN_SEMICOLON, "Expect ';' after value.");
    emitByte(OP_INPUT);
}

static void synchronize() {
    parser.panicMode = false;

    while(parser.current.type != TOKEN_EOF) {
        if(parser.previous.type == TOKEN_SEMICOLON) return;
        switch(parser.current.type) {
            case TOKEN_CLASS:
            case TOKEN_FUN:
            case TOKEN_VAR:
            case TOKEN_CONST:
            case TOKEN_FOR:
            case TOKEN_IF:
            case TOKEN_WHILE:
            case TOKEN_PRINT:
            case TOKEN_RETURN:
                return;
            default: break; 
        }
        advance();
    }
}

static void block() {
    while(!check(TOKEN_RIGHT_BRACE) && !check(TOKEN_EOF)) {
        declaration();
    }
    consume(TOKEN_RIGHT_BRACE, "Expect '}' after block.");
}

static void beginScope() {
    current->scopeDepth++;
}

static void endScope() {
    current->scopeDepth--;
    while(current->localCount > 0 && current->locals[current->localCount - 1].depth == current->scopeDepth) {
        emitByte(OP_POP);
        current->localCount--;
    }
}

static void varDeclaration(bool isconst) {
    if(!isconst) {
        uint16_t global = parseVariable("Expect variable name.", false);
        if (match(TOKEN_EQUAL)) {
            expression();
        } else {
            emitByte(OP_NV);
        }
        consume(TOKEN_SEMICOLON, "Expect ';' after variable declaration.");
        defineVariable(global, false);
    } else {
        uint16_t global = parseVariable("Expect variable name.", true);
        if (match(TOKEN_EQUAL)) {
            expression();
        } else {
            emitByte(OP_NV);
        }
        consume(TOKEN_SEMICOLON, "Expect ';' after variable declaration.");
        defineVariable(global, true);
    }
}

static void or_(bool canAssign) {
    int elseJump = emitJump(OP_JUMP_IF_FALSE);
    int endJump = emitJump(OP_JUMP);

    patchJump(elseJump);
    emitByte(OP_POP);
    parsePrecedence(PREC_OR);
    patchJump(endJump);
}

static void and_(bool canAssign) {
    int endJump = emitJump(OP_JUMP_IF_FALSE);
    emitByte(OP_POP);
    parsePrecedence(PREC_AND);
    patchJump(endJump);
}

static void ifStatement() {
    consume(TOKEN_LEFT_PAREN, "Expect '(' after 'if'.");
    expression();
    consume(TOKEN_RIGHT_PAREN, "Expect ')' after condition.");

    int thenJump = emitJump(OP_JUMP_IF_FALSE);
    emitByte(OP_POP);
    statement();

    int elseJump = emitJump(OP_JUMP);
    emitByte(OP_POP);
    patchJump(thenJump);
    if(match(TOKEN_ELSE)) {
        patchJump(elseJump);
    }   
}

static void whileStatement() {
    int loopStart = currentChunk()->count;
    consume(TOKEN_LEFT_PAREN, "Expect '(' after 'while'.");
    expression();
    consume(TOKEN_RIGHT_PAREN, "Expect ')' after condition.");

    int exitJump = emitJump(OP_JUMP_IF_FALSE);
    emitByte(OP_POP);
    statement();
    emitLoop(loopStart);
    
    patchJump(exitJump);
    emitByte(OP_POP);
}

static void statement() {
    if (match(TOKEN_PRINT)) {
        printStatement();
    }
    else if(match(TOKEN_IF)) {
        ifStatement();
    }
    else if(match(TOKEN_LEFT_BRACE)) {
        beginScope();
        block();
        endScope();
    } else if(match(TOKEN_WHILE)) {
        whileStatement();
    }
    else {

    }
}

static void declaration() {
    if (match(TOKEN_VAR)) {
        varDeclaration(false);
    } else if(match(TOKEN_CONST)) {
        varDeclaration(true);
    }
    else {
        statement();
    }
    if (parser.panicMode) synchronize();
}

static void endCompiler() {
    emitReturn();
    #ifdef DEBUG_PRINT_CODE
    if(!parser.hadError) {
        disassembleChunk(currentChunk(), "code");
    }
    #endif
}

static void expression();
static ParseRule* getRule(TokenType type);
static void parsePrecedence(Precedence precedence);
static void grouping(bool canAssign);
static void unary(bool canAssign);
static void binary(bool canAssign);
static void number(bool canAssign);
static void string(bool canAssign);
static void variable(bool canAssign);

static void binary(bool canAssign) {
   TokenType operatorType = parser.previous.type;
   ParseRule* rule = getRule(operatorType);
   parsePrecedence((Precedence)(rule->precedence + 1));

   switch(operatorType) {
        case TOKEN_MINUS: emitByte(OP_SUBTRACT); break;
        case TOKEN_PLUS: emitByte(OP_ADD); break;
        case TOKEN_STAR: emitByte(OP_MULTIPLY); break;
        case TOKEN_SLASH: emitByte(OP_DIVIDE); break;
        case TOKEN_POW: emitByte(OP_POW); break;
        case TOKEN_BANG_EQUAL: emitByte(OP_NE); break;
        case TOKEN_EQUAL_EQUAL: emitByte(OP_EE); break;
        case TOKEN_GREATER: emitByte(OP_GREATER); break;
        case TOKEN_GREATER_EQUAL: emitByte(OP_GTE); break;
        case TOKEN_LESS: emitByte(OP_LESS); break;
        case TOKEN_LESS_EQUAL: emitByte(OP_LTE); break;
        default: return;
   }
}

static void literal(bool canAssign) {
    switch(parser.previous.type) {
        case TOKEN_FALSE: emitByte(OP_FALSE); break;
        case TOKEN_TRUE: emitByte(OP_TRUE); break;
        case TOKEN_NIL: emitByte(OP_NIL); break; 
    }
}

static void number(bool canAssign) {
    double value = strtod(parser.previous.start, NULL);
    emitConstant(NUMBER_VAL(value)); 
}

static void string(bool canAssign) {
    emitConstant(OBJ_VAL(copyString(parser.previous.start + 1,
                                  parser.previous.length - 2)));
}

static int resolveLocal(Compiler* compiler, Token* name) {
    for (int i = compiler->localCount - 1; i >= 0; i--) {
        Local* local = &compiler->locals[i];
        if (identifiersEqual(name, &local->name)) {
            if (local->depth == -1) {
                error("Can't read local variable in its own initializer.");
            }
            return i;
        }
    }
    return -1;
}

static void namedVariable(Token name, bool canAssign) {
    uint16_t getOp, setOp;
    int local = resolveLocal(current, &name);
    int constant;
    if (local != -1) {
       getOp = OP_GET_LOCAL;
       setOp = OP_SET_LOCAL;
       constant = local;
    } else {
        constant = identifierConstant(&name);
        getOp = OP_GET_GLOBAL;
        setOp = OP_DEFINE_GLOBAL;
    }
    if (canAssign && match(TOKEN_EQUAL)) {
        if(local != -1 && current->locals[local].isConst) {
            error("Can't assign to a constant variable."); 
        }
        expression();
        emitByte(setOp);
        emitByte((constant >> 8) & 0xff);
        emitByte(constant & 0xff);
    } else {
        emitByte(getOp);
        emitByte((constant >> 8) & 0xff);
        emitByte(constant & 0xff);
    }
}

static void variable(bool canAssign) {
    namedVariable(parser.previous, canAssign);
}

static void unary(bool canAssign) {
    TokenType operatorType = parser.previous.type;

    parsePrecedence(PREC_UNARY);
    
    switch(operatorType) {
        case TOKEN_BANG: emitByte(OP_NOT); break;
        case TOKEN_MINUS: emitByte(OP_NEGATE); break;
        default: return;
    }
}



static void grouping(bool canAssign) {
    expression();
    consume(TOKEN_RIGHT_PAREN, "Expect ')' after expression."); 
}


bool compile(const char* source, Chunk* chunk) {
    initScanner(source);
    Compiler compiler;
    initCompiler(&compiler);
    compilingChunk = chunk;
    initChunk(chunk);
    parser.hadError = false;
    parser.panicMode = false;

    advance();
    while (!match(TOKEN_EOF)) {
        declaration();
    }
    endCompiler();
    return !parser.hadError;
}