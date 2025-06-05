// void test(char *arg);
#include <stdint.h>
#include <stddef.h>

void wg_send(void* plaintext, size_t plaintext_len, uint32_t peer, void* send_key, size_t send_key_len, size_t nonce, void* obuf, size_t obuf_len);

void wg_recv(uint32_t peer, void* recv_key, size_t recv_key_len, size_t nonce, void* buf, size_t buf_len);