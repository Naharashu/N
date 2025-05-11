#include "compile.h"
#include "scanner.h"
#include "common.h"

void compile(const char* source) {
    initScanner(source);
    int line = -1;
    for(;;) {
        Token token = scanToken();
        if(token.line != line) {
            printf("%d ", token.line);
            line = token.line;
        } else { 
            printf("|");
        }
        printf("%d '%.*s'\n", token.type, token.length, token.start);
        if(token.type == TOKEN_EOF) break;
    }
}