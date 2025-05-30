#include "common.h"
#include "vm.h"
#include "debug.h"
#include "compile.h"
#include <math.h>
#include <stdarg.h>
#include <string.h>
#include "memory.h"
#include "object.h"
#include <time.h>

VM vm;

static Value peek(int distance);
static void runtimeError(const char *format, ...);

static bool isFalsey(Value value)
{
    return IS_NIL(value) || (IS_BOOL(value) && !AS_BOOL(value));
}

static void concatenate() {
    ObjString* b = AS_STRING(pop());
  ObjString* a = AS_STRING(pop());

  int length = a->length + b->length;
  char* chars = ALLOCATE(char, length + 1);
  memcpy(chars, a->chars, a->length);
  memcpy(chars + a->length, b->chars, b->length);
  chars[length] = '\0';

  ObjString* result = takeString(chars, length);
  push(OBJ_VAL(result));
}

static interpretResult run()
{
#define READ_BYTE() (*vm.ip++)
#define READ_SHORT() \
    (vm.ip += 2, (uint16_t)((vm.ip[-2] << 8) | vm.ip[-1]))
#define READ_CONSTANT() (vm.chunk->constants.values[READ_SHORT()])
#define READ_STRING() AS_STRING(READ_CONSTANT())
#define BINARY_OP(valueType, op)                        \
    do                                                  \
    {                                                   \
        if (!IS_NUMBER(peek(0)) || !IS_NUMBER(peek(1))) \
        {                                               \
            runtimeError("Operands must be numbers.");  \
            return INTERPRETER_RUNTIME_ERROR;           \
        }                                               \
        double b = AS_NUMBER(pop());                    \
        double a = AS_NUMBER(pop());                    \
        push(valueType(a op b));                        \
    } while (false)

    for (;;)
    {
#ifdef DEBUG_TRACE_EXECUTION
        printf("");
        for (Value *slot = vm.stack; slot < vm.stackTop; slot++)
        {
            printf("[ ");
            printValue(*slot);
            printf(" ]");
        }
        printf("\n");
        disassembleInstruction(vm.chunk, (int)(vm.ip - vm.chunk->code));
#endif
        uint8_t instruction;
        switch (instruction = READ_BYTE())
        {
        case OP_CONSTANT:
        {
            Value cosnt = READ_CONSTANT();
            push(cosnt);
            break;
        }
        case OP_ADD:
        {
            if (IS_STRING(peek(0)) && IS_STRING(peek(1)))
            {
                concatenate();
            }
            else if (IS_NUMBER(peek(0)) && IS_NUMBER(peek(1)))
            {
                double b = AS_NUMBER(pop());
                double a = AS_NUMBER(pop());
                push(NUMBER_VAL(a + b));
            } else {
                runtimeError("You can only add string(concat) or numbers(binary)");
                return INTERPRETER_RUNTIME_ERROR;
            }
            break;
        }
        case OP_SUBTRACT:
            BINARY_OP(NUMBER_VAL, -);
            break;
        case OP_MULTIPLY:
            BINARY_OP(NUMBER_VAL, *);
            break;
        case OP_DIVIDE:
            BINARY_OP(NUMBER_VAL, /);
            break;
        case OP_POW:
        {
            double exponent = AS_NUMBER(pop());
            double base = AS_NUMBER(pop());
            push(NUMBER_VAL(pow(base, exponent)));
            break;
        }
        case OP_NIL:
            push(NIL_VAL);
            break;
        case OP_NV: {
            push(NIL_VAL);
            break;
        }
        case OP_TRUE:
            push(BOOL_VAL(true));
            break;
        case OP_FALSE:
            push(BOOL_VAL(false));
            break;
        case OP_POP: pop(); break;
        case OP_GET_GLOBAL: {
            ObjString* name = READ_STRING();
            Value value;
            if (!tableGet(&vm.globals, name, &value)) {
                runtimeError("Undefined variable '%s'.", name->chars);
                return INTERPRETER_RUNTIME_ERROR;
            }
            push(value);
            break;
        }
        case OP_DEFINE_GLOBAL: {
            ObjString* name = READ_STRING();
            tableSet(&vm.globals, name, peek(0), false);
            pop();
            break;
        }
        case OP_DEFINE_GLOBAL_CONST: {
            ObjString* name = READ_STRING();
            tableSet(&vm.globals, name, peek(0), true);
            pop();
            break;
        }
        case OP_SET_GLOBAL: {
            ObjString* name = READ_STRING();
            if (!tableUpdate(&vm.globals, name, peek(0))) {
                runtimeError("Can't assign to constant variable '%s'.", name->chars);
                return INTERPRETER_RUNTIME_ERROR;
            }
            break;
        }
        case OP_GET_LOCAL: {
            uint16_t slot = READ_SHORT();
            push(vm.stack[slot]);
            break;
        }
        case OP_SET_LOCAL: {
            uint16_t slot = READ_SHORT();
            vm.stack[slot] = peek(0);
            break;
        }
        case OP_NOT:
        {
            push(BOOL_VAL(isFalsey(pop())));
            break;
        }
        case OP_EE:
        {
            Value a = pop();
            Value b = pop();
            push(BOOL_VAL(valuesEE(a, b)));
            break;
        }
        case OP_LESS:
            BINARY_OP(BOOL_VAL, <);
            break;
        case OP_LTE:
            BINARY_OP(BOOL_VAL, <=);
            break;
        case OP_GREATER:
            BINARY_OP(BOOL_VAL, >);
            break;
        case OP_GTE:
            BINARY_OP(BOOL_VAL, >=);
            break;
        case OP_NEGATE:
        {
            if (!IS_NUMBER(peek(0)))
            {
                runtimeError("Operand must be a number.");
                return INTERPRETER_RUNTIME_ERROR;
            }
            push(NUMBER_VAL(-AS_NUMBER(pop())));
            break;
        }
        case OP_PRINT: {
            printValue(pop());
            printf("\n");
            break;
        }
        case OP_INPUT: {
            char buffer[1024];
            fgets(buffer, 1024, stdin);
            if (buffer[strlen(buffer) - 1] == '\n') {
                buffer[strlen(buffer) - 1] = '\0';
            }
            push(OBJ_VAL(takeString(buffer, strlen(buffer))));
            break;
        }
        case OP_JUMP_IF_FALSE: {
            uint16_t offset = READ_SHORT();
            if(isFalsey(peek(0))) vm.ip += offset;
            break;  
        }
        case OP_JUMP: {
            uint16_t offset = READ_SHORT();
            vm.ip += offset;
            break;
        }
        case OP_LOOP: {
            uint16_t offset = READ_SHORT();
            vm.ip -= offset;
            break;
        }
        case OP_RETURN:
        {
            return INTERPRETER_OK;
        }
        }
    }
#undef READ_BYTE
#undef READ_SHORT
#undef READ_CONSTANT
#undef READ_STRING
#undef BINARY_OP
}

static void resetStack()
{
    vm.stackTop = vm.stack;
}

static void runtimeError(const char *format, ...)
{
    va_list args;
    va_start(args, format);
    vfprintf(stderr, format, args);
    va_end(args);
    fputs("\n", stderr);
    size_t instruction = vm.ip - vm.chunk->code - 1;
    int line = vm.chunk->lines[instruction];
    fprintf(stderr, "[line %d] in script\n", line);
    resetStack();
}

void initVM()
{
    resetStack();
    vm.objects = NULL;
    initTable(&vm.globals);
    initTable(&vm.strings);
}

void freeVM()
{
    resetStack();
    freeTable(&vm.globals);
    freeTable(&vm.strings);
    freeObjects();
}

void push(Value value)
{
    *vm.stackTop = value;
    vm.stackTop++;
}

Value pop()
{
    vm.stackTop--;
    return *vm.stackTop;
}

static Value peek(int distance)
{
    return vm.stackTop[-1 - distance];
}

static Entry* findEntry(Entry* entries, int capacity, ObjString* key) {
    uint32_t index = key->hash % capacity;
    Entry* tombstone = NULL;
    for(;;) {
        Entry* entry = &entries[index];
        if (entry->key == NULL) {
            if (IS_NIL(entry->value)) {
                return tombstone != NULL ? tombstone : entry;
            } else {
                if (tombstone != NULL) tombstone = entry;
            }
        } else if (entry->key == key) {
            return entry;
        }
        index = (index + 1) % capacity;
    }
}

interpretResult interpret(const char *source)
{
    Chunk chunk;
    initChunk(&chunk);

    if (!compile(source, &chunk))
    {
        freeChunk(&chunk);
        return INTERPRETER_COMPILE_ERROR;
    }

    vm.chunk = &chunk;
    vm.ip = vm.chunk->code;

    interpretResult result = run();

    freeChunk(&chunk);
    return result;
}
