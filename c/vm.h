#ifndef vm_h
#define vm_h

#include "chunk.h"
#include "value.h"
#include "table.h"
#define STACK_MAX 256
typedef struct {
    Chunk* chunk;
    uint8_t* ip;
    Value stack[STACK_MAX];
    Value* stackTop;
    Table globals;
    Table strings;
    Obj* objects;
} VM;

typedef enum {
    INTERPRETER_OK,
    INTERPRETER_COMPILE_ERROR,
    INTERPRETER_RUNTIME_ERROR
} interpretResult;

extern VM vm;

void initVM();
void freeVM();
interpretResult interpret(const char* source);
void push(Value value);
Value pop();

#endif