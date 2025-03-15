#include<stdint.h>

uint32_t add(uint32_t a, uint32_t b) {
    return a + b;
}

void ascii_to_upper(char *str) {
    while (*str) {
        if (*str >= 'a' && *str <= 'z') {
            *str -= 32;
        }

        str++;
    }
}