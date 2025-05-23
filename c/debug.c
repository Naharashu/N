#include <stdio.h>
#include "debug.h"
#include "value.h"


void disassembleChunk(Chunk* chunk, const char* name) {
    printf("== %s ==\n", name);
    for (int offset = 0; offset < chunk->count;) {
        offset = disassembleInstruction(chunk, offset);
    }
}

static int simpleInstruction(const char* name, int offset) {
    printf("%s\n", name);
    return offset + 1;
}

static int bytesInstruction(const char* name, Chunk* chunk,
                           int offset) {
  uint16_t slot = chunk->code[offset + 1];
  printf("%-16s %4d\n", name, slot);
  return offset + 2; 
}

static int constantInstruction(const char* name, Chunk* chunk, int offset) {
    uint16_t constant = (chunk->code[offset + 1] << 8) | chunk->code[offset + 2];
    printf("%-16s %4d '", name, constant);
    printValue(chunk->constants.values[constant]);
    printf("'\n");
    return offset + 3;
}

int disassembleInstruction(Chunk* chunk, int offset) {
    printf("%04d ", offset);
    if (offset > 0 && chunk->lines[offset] == chunk->lines[offset - 1]) {
        printf("|");
    } else {
        printf("%4d ", chunk->lines[offset]);
    }
    uint8_t instruction = chunk->code[offset];
    switch (instruction) {
        case OP_RETURN:
            return simpleInstruction("OP_RETURN", offset);
        case OP_CONSTANT:
            return constantInstruction("OP_CONSTANT", chunk, offset);
        case OP_ADD:
            return simpleInstruction("OP_ADD", offset);
        case OP_SUBTRACT:
            return simpleInstruction("OP_SUBTRACT", offset);
        case OP_MULTIPLY:
            return simpleInstruction("OP_MULTIPLY", offset);
        case OP_DIVIDE:
            return simpleInstruction("OP_DIVIDE", offset);
        case OP_POW:
            return simpleInstruction("OP_POW", offset);
        case OP_NIL:
            return simpleInstruction("OP_NIL", offset);
        case OP_TRUE:
            return simpleInstruction("OP_TRUE", offset);
        case OP_FALSE:
            return simpleInstruction("OP_FALSE", offset);
        case OP_POP:
            return simpleInstruction("OP_POP", offset);
        case OP_GET_GLOBAL:
            return constantInstruction("OP_GET_GLOBAL", chunk, offset);
        case OP_DEFINE_GLOBAL:
            return constantInstruction("OP_DEFINE_GLOBAL", chunk, offset);
        case OP_SET_GLOBAL:
            return constantInstruction("OP_SET_GLOBAL", chunk, offset);
        case OP_SET_LOCAL:
            return bytesInstruction("OP_SET_LOCAL", chunk, offset);
        case OP_GET_LOCAL:
            return bytesInstruction("OP_GET_LOCAL", chunk, offset);
        case OP_DEFINE_GLOBAL_CONST:
            return constantInstruction("OP_DEFINE_GLOBAL_CONST", chunk, offset);
        case OP_NOT:
            return simpleInstruction("OP_NOT", offset);
        case OP_EE:
            return simpleInstruction("OP_EE", offset);
        case OP_GREATER:
            return simpleInstruction("OP_GREATER", offset);
        case OP_LESS:
            return simpleInstruction("OP_LESS", offset);
        case OP_LTE:
            return simpleInstruction("OP_LTE", offset);
        case OP_GTE:
            return simpleInstruction("OP_GTE", offset);
        case OP_NEGATE:
            return simpleInstruction("OP_NEGATE", offset);
        case OP_PRINT:
            return simpleInstruction("OP_PRINT", offset);
        case OP_JUMP:
            return bytesInstruction("OP_JUMP", chunk, offset);
        case OP_JUMP_IF_FALSE:
            return bytesInstruction("OP_JUMP_IF_FALSE", chunk, offset);
        case OP_LOOP:
            return bytesInstruction("OP_LOOP", chunk, offset);
        default:
            printf("Unknown opcode %d\n", instruction);
            return offset + 1;
    }
}

