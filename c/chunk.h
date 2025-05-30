#ifndef chunk_h
#define chunk_h

#include "common.h"
#include "value.h"

typedef enum {
    OP_CONSTANT,
    OP_NEGATE,
    OP_NIL,
    OP_NV,
    OP_TRUE,
    OP_FALSE,
    OP_POP,
    OP_GET_GLOBAL,
    OP_DEFINE_GLOBAL,
    OP_DEFINE_GLOBAL_CONST, 
    OP_SET_GLOBAL,
    OP_GET_LOCAL,
    OP_SET_LOCAL,
    OP_NOT,
    OP_EE,
    OP_LESS,
    OP_GREATER,
    OP_NE,
    OP_GTE,
    OP_LTE,
    OP_ADD,
    OP_SUBTRACT,
    OP_MULTIPLY,
    OP_DIVIDE,
    OP_POW,
    OP_PRINT,
    OP_INPUT,
    OP_JUMP_IF_FALSE,
    OP_JUMP,
    OP_LOOP,
    OP_RETURN,
} OpCode;

typedef struct {
    int count;
    int capacity;
    uint8_t * code;
    ValueArray constants;
    int* lines;
} Chunk;

void initChunk(Chunk * chunk);
void writeChunk(Chunk * chunk, uint8_t byte, int line);
int addConstant(Chunk * chunk, Value value);
void freeChunk(Chunk *chunk);

#endif