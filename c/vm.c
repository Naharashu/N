#include "common.h"
#include "vm.h"
#include "debug.h"
#include "compile.h"

VM vm;

static interpretResult run() {
    #define READ_BYTE() (*vm.ip++)
    #define READ_CONSTANT() (vm.chunk->constants.values[READ_BYTE()])
    #define BINARY_OP(op) \
        do { \
        double b = pop(); \
        double a = pop(); \
        push(a op b); \
        } while (false)

    for(;;) {
        #ifdef DEBUG_TRACE_EXECUTION
            printf("");
            for(Value* slot = vm.stack; slot < vm.stackTop; slot++) {
                printf("[ ");
                printValue(*slot);
                printf(" ]");
            }
            printf("\n");
            disassembleInstruction(vm.chunk, (int)(vm.ip - vm.chunk->code));
        #endif
        uint8_t instruction;
        switch(instruction = READ_BYTE()) {
            case OP_CONSTANT: {
                Value cosnt = READ_CONSTANT();
                push(cosnt);
                break;
            }
            case OP_ADD: BINARY_OP(+); break;
            case OP_SUBTRACT: BINARY_OP(-); break;
            case OP_MULTIPLY: BINARY_OP(*); break;
            case OP_DIVIDE: BINARY_OP(/); break;
            case OP_NEGATE: {
                push(-pop());
                break;
            }
            case OP_RETURN: {
                printValue(pop());
                printf("\n");
                return INTERPRETER_OK;
            }
        }
    }
    #undef READ_BYTE
    #undef READ_CONSTANT
    #undef BINARY_OP
}

static void resetStack() {
    vm.stackTop = vm.stack;
}

void initVM() {
    resetStack();
}

void freeVM() {
    resetStack();
}

void push(Value value) {
    *vm.stackTop = value;
    vm.stackTop++;
}

Value pop() {
    vm.stackTop--;
    return *vm.stackTop;
}
interpretResult interpret(const char* source) {
    compile(source);
    return INTERPRETER_OK;
}

