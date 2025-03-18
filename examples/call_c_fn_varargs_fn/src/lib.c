#include<stdarg.h>
#include<stdint.h>

uint32_t vararg_sum(uint32_t n_numbers, ...) {
    uint32_t sum = 0;
    va_list args;
    va_start(args, n_numbers);

    for (int i = 0; i < n_numbers; i++) {
        sum += va_arg(args, int);
    }

    va_end(args);
    return sum;
}

void ascii_to_upper(char *str) {
    while (*str) {
        if (*str >= 'a' && *str <= 'z') {
            *str -= 32;
        }

        str++;
    }
}