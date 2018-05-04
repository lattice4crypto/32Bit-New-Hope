# - Creates the public and private keys, encrypts and decrypts a 32-byte message

import logging
import os
import sys
import hashlib
import random
from logging import debug, warning, info
import datetime as dt

NEWHOPE_N = 1024      # Security level of 233 (sect. 1.3 of NewHope supporting document)
NEWHOPE_N_INV = 12277   # inverse of n
NEWHOPE_7N_4 = 1792     # 7n/4
NEWHOPE_3N_8 = 384      # 3n/4
NEWHOPE_Q = 12289     # Smallest prime st. q = 1 (mod 2n) so that NTT can be realized efficiently (sect. 1.3)
NEWHOPE_K  =8         # Distribution of RLWE secret using centered binomial distribution of parameter k=8 (sect. 1.3)
NEWHOPE_ROOT = 10302    # square root of nth root of unity
SQUEEZE_BLOCK_SIZE = 168    # block size of SHAKE output

# Generates a randomly distributed polynomial in Rq
def GenA(publicseed):

    debug("Generating the polynomial a_hat")
    a_hat = [0]*NEWHOPE_N   # Declare polynomial of size NEWHOPE_N with 0 coefficients

    debug("Initializing extseed")
    extseed = bytearray(33)
    extseed[0:32] = publicseed[0:32]

    debug("Starting loop")
    for i in range(0, (NEWHOPE_N//64)):
        ctr = 0
        extseed[32] = i
        state = hashlib.shake_128(extseed)
        while ctr < 64:
            buf = state.digest(SQUEEZE_BLOCK_SIZE*1)
            j = 0
            while (j<168) and (ctr<64):     # The algorithm has this in a for-loop, but this while loop is equivalent
                buf0 = int(buf[j])
                buf1 = (int(buf[j+1]) << 8) % 4294967296      # 2^32 = 4294967296
                val = buf0|buf1
                if val<(5*NEWHOPE_Q):
                    a_hat[(64*i)+ctr] = val % NEWHOPE_Q
                    ctr += 1
                j += 2

    debug("Done generating a_hat")
    return a_hat

# Samples the R-LWE secret and error
def Sample(noiseseed, nonce):

    debug("Sampling a random polynomial in Rq")
    r = [0]*NEWHOPE_N   # Declare polynomial of size NEWHOPE_N

    debug("Initializing extseed and setting nonce ")
    extseed = bytearray(34)
    extseed[0:32] = noiseseed[0:32]
    extseed[32] = nonce

    debug("Starting loop")
    for i in range(0, (NEWHOPE_N//64)):     # Generate noise in lbocks of 64 coefficients
        extseed[33] = i
        buf = hashlib.shake_256(extseed).digest(128)
        for j in range(0, 64):
            a = buf[2*j]
            b = buf[(2*j)+1]
            r[(64*i)+j] = (bin(a).count("1") + NEWHOPE_Q - bin(b).count("1")) % NEWHOPE_Q

    debug("Done sampling random polynomial in Rq")
    return r

# Multiplies two polynomials coefficient-wise
def Poly_mul(a, b):
    c = [0]*NEWHOPE_N
    for i in range(0, NEWHOPE_N):
        c[i] = (a[i]*b[i]) % NEWHOPE_Q
    return c

# Adds two polynomials coefficient-wise
def Poly_add(a, b):
    c = [0]*NEWHOPE_N
    for i in range(0, NEWHOPE_N):
        c[i] = (a[i]+b[i]) % NEWHOPE_Q
    return c

# Subtracts two polynomials coefficient-wise
def PolySubtract(a, b):
    c = [0]*NEWHOPE_N
    for i in range(0, NEWHOPE_N):
        c[i] = (a[i]-b[i]) % NEWHOPE_Q
    return c

# # Implementation from Patrick Longa and Michael Naehrig
# # - Algorithm 1: NTT
# # Title: "Speeding up the Number Theoretic Transform for Faster Ideal Lattice-Based Cryptography"
# # URL: "https://eprint.iacr.org/2016/504.pdf"
# def NTT(a):
#
#     debug("Starting NTT")
#     t = NEWHOPE_N
#     m = 1
#
#     debug("Beginning while-loop in NTT")
#     while(m < NEWHOPE_N):
#         t = t//2
#         for i in range(0, m):
#             j1 = 2*i*t
#             j2 = j1 + t - 1
#             s = psi_bitrev[m+i]
#             for j in range(j1, j2+1):
#                 u = a[j]
#                 v = a[j+t]*s
#                 a[j] = (u+v) % NEWHOPE_Q
#                 a[j+t] = (u-v) % NEWHOPE_Q
#         m = 2*m
#     debug("End of while-loop in NTT")
#     return a
#
# # Implementation from Patrick Longa and Michael Naehrig
# # - Algorithm 2: INTT
# # Title: "Speeding up the Number Theoretic Transform for Faster Ideal Lattice-Based Cryptography"
# # URL: "https://eprint.iacr.org/2016/504.pdf"
# def INTT(a):
#     t = 1
#     m = NEWHOPE_N
#     while (m > 1):
#         j1 = 0
#         h = m//2
#         for i in range(0, h):
#             j2 = j1 + t - 1
#             s = psi_bitrev_inv[h+1]
#             for j in range(j1, j2+1):
#                 u = a[j]
#                 v = a[j+1]
#                 a[j] = (u+v) % NEWHOPE_Q
#                 a[j+t] = (u-v)*s % NEWHOPE_Q
#             j1 = j1 + (2*t)
#         t = 2*t
#         m = m//2
#     for j in range(0, NEWHOPE_N):
#         a[j] = (a[j]*NEWHOPE_N_INV) % NEWHOPE_Q
#     return a

# Returns the forward number-theoretic transform of the given vector with
# respect to the given primitive nth root of unity under the given modulus.
def NTT(invec, root, mod):
	outvec = []
	for i in range(len(invec)):
		temp = 0
		for (j, val) in enumerate(invec):
			temp += val * pow(root, i * j, mod)
			temp %= mod
		outvec.append(temp)
	return outvec


# Returns the inverse number-theoretic transform of the given vector with
# respect to the given primitive nth root of unity under the given modulus.
def INTT(invec, root, mod):
	outvec = NTT(invec, reciprocal(root, mod), mod)
	scaler = reciprocal(len(invec), mod)
	return [(val * scaler % mod) for val in outvec]

# Returns the multiplicative inverse of n modulo mod. The inverse x has the property that
# 0 <= x < mod and (x * n) % mod = 1. The inverse exists if and only if gcd(n, mod) = 1.
def reciprocal(n, mod):
	if not (0 <= n < mod):
		raise ValueError()
	x, y = mod, n
	a, b = 0, 1
	while y != 0:
		a, b = b, a - x // y * b
		x, y = y, x % y
	if x == 1:
		return a % mod
	else:
		raise ValueError("Reciprocal does not exist")

# Encodes the ciphertext and error
def EncodeC(u, h):
    c = [0]*(NEWHOPE_7N_4 + NEWHOPE_3N_8)
    c[0:NEWHOPE_7N_4] = EncodePoly(u)
    c[NEWHOPE_7N_4:] = h
    return c

# Encodes a polynomial in Rq as an array of bytes
def EncodePoly(s):
    r = [0]*NEWHOPE_7N_4
    for i in range(0, 256):
        t0 = s[(4*i)+0] % NEWHOPE_Q
        t1 = s[(4*i)+1] % NEWHOPE_Q
        t2 = s[(4*i)+2] % NEWHOPE_Q
        t3 = s[(4*i)+3] % NEWHOPE_Q
        r[(7*i)+0] = t0 & int(0xff)
        r[(7*i)+1] = (t0 >> 8) | ((t1 << 6)%4294967296) & int(0xff)
        r[(7*i)+2] = (t1 >> 2) & int(0xff)
        r[(7*i)+3] = (t1 >> 10) | ((t2 << 4)%4294967296) & int(0xff)
        r[(7*i)+4] = (t2 >> 4) & int(0xff)
        r[(7*i)+5] = (t2 >> 12) | ((t3 << 2)%4294967296) & int(0xff)
        r[(7*i)+6] = (t3 >> 6) & int(0xff)
    return r

# Encodes the public key
def EncodePK(b_hat, publicseed):
    r = [0]*(NEWHOPE_7N_4 + 32)
    r[0:NEWHOPE_7N_4] = EncodePoly(b_hat)
    r[NEWHOPE_7N_4:] = publicseed
    return r

# Encodes the 32-byte message to a polynomial in Rq
def EncodeMsg(m):
    v = [0]*NEWHOPE_N
    for i in range(0, 32):
        for j in range(0, 8):
            mask = -(((m[i]>>j))&1)
            v[(8*i)+j+0] = (mask&(NEWHOPE_Q//2)) #% NEWHOPE_Q
            v[(8*i)+j+256] = (mask&(NEWHOPE_Q//2)) #% NEWHOPE_Q
            v[(8*i)+j+512] = (mask&(NEWHOPE_Q//2)) #% NEWHOPE_Q
            v[(8*i)+j+768] = (mask&(NEWHOPE_Q//2)) #% NEWHOPE_Q
    return v

# Decodes the ciphertext and error
def DecodeC(c):
    u = DecodePoly(c[0:NEWHOPE_7N_4])
    h = c[NEWHOPE_7N_4:]
    return u, h

# Decodes an array of bytes to a polynomial in Rq
def DecodePoly(v):
    debug('Starting decoding polynomial')
    r = [0]*NEWHOPE_N
    for i in range(0, 256):
        r[(4*i)+0] = int(v[(7*i)+0]) | (((int(v[(7*i)+1])&int(0x3f))<<8)%4294967296)
        r[(4*i)+1] = (int(v[(7*i)+1]) >> 6) | ((int(v[(7*i)+2]) << 2)%4294967296) | (((int(v[(7*i)+3])&int(0x0f))<<10)%4294967296)
        r[(4*i)+2] = (int(v[(7*i)+3]) >> 4) | ((int(v[(7*i)+4]) << 4)%4294967296) | (((int(v[(7*i)+5])&int(0x03))<<12)%4294967296)
        r[(4*i)+3] = (int(v[(7*i)+5]) >> 2) | ((int(v[(7*i)+6]) << 6)%4294967296)
    debug('Done decoding polynomial')
    return r

# Encodes the 32-byte message to a polynomial in Rq
def DecodeMsg(v):
    m = [0]*32
    for i in range(0, 256):
        t = abs(((v[i+0])%NEWHOPE_Q) - ((NEWHOPE_Q)//2))
        t = t + abs((((v[i+256])%NEWHOPE_Q) - ((NEWHOPE_Q)//2)))
        t = t + abs((((v[i+512])%NEWHOPE_Q) - ((NEWHOPE_Q)//2)))
        t = t + abs((((v[i+768])%NEWHOPE_Q) - ((NEWHOPE_Q)//2)))
        t = t - NEWHOPE_Q
        t = t >> 15
        m[i>>3] = m[i>>3] | -(t<<(i&7))
    return m

# Decodes the public key
def DecodePK(pk):
    debug('Starting decoding public key')
    b_hat = DecodePoly(pk[0:NEWHOPE_7N_4])
    seed = pk[NEWHOPE_7N_4:]
    debug('Done decoding public key')
    return b_hat, seed

# Compresses a message to send
def Compress(v):
    k = 0
    t = [0]*8
    h = [0]*NEWHOPE_3N_8
    for l in range(0, 128):
        i = 8*l
        for j in range(0, 8):
            t[j] = v[i+j] % NEWHOPE_Q
            t[j] = (((int(t[j]<<3))+NEWHOPE_Q//2)//NEWHOPE_Q) & int(0x7)
        h[k+0] = (t[0] | ((t[1]<<3)) | ((t[2]<<6))) #%256
        h[k+1] = ((t[2]>>2) | ((t[3]<<1)) | ((t[4]<<4)) | ((t[5]<<7))) #%256
        h[k+2] = ((t[5]>>1) | ((t[6]<<2)) | ((t[7]<<5))) #%256
        # print("============================compress================================")
        # print(h)
        # print("============================compress================================")
        k += 3
    return h

# Decompresses the message to recover the data
def Decompress(h):
    r = [0]*NEWHOPE_N
    k = 0
    # print("============================input================================")
    # print(h)
    # print("============================input================================")
    for l in range(0, 128):
        i = 8*l
        r[i+0] = h[k+0] & 7
        r[i+1] = (h[k+0]>>3) & 7
        r[i+2] = (h[k+0]>>6) | (((h[1]<<2))&4)
        r[i+3] = (h[k+1]>>1) & 7
        r[i+4] = (h[k+1]>>4) & 7
        r[i+5] = (h[k+1]>>7) | (((h[2]<<1))&6)
        r[i+6] = (h[k+2]>>2) & 7
        r[i+7] = (h[k+2]>>5)
        k += 3
        # print("============================decompress================================")
        # print(r)
        # print("============================decompress================================")
        for j in range(0, 8):
            r[i+j] = (((r[i+j])*NEWHOPE_Q)+4)>>3
    return r

# Generates the public and private key
def PKEGen():

    debug("Generating the 32-byte random seed")
    seed = os.urandom(32)

    debug("Creating publicseed and noiseseed")
    z = hashlib.shake_256(seed).digest(64)
    publicseed = z[0:32]
    noiseseed = z[32:]

    debug("Generating polynomial a_hat")
    a_hat = GenA(publicseed)

    debug("Sampling polynomial s")
    s = Sample(noiseseed, 0)

    debug("Computing s_hat = NTT of s")
    s_hat = NTT(s, NEWHOPE_ROOT, NEWHOPE_Q)

    debug("Sampling polynomial e")
    e = Sample(noiseseed, 1)

    debug("Computing e_hat = NTT of e")
    e_hat = NTT(e, NEWHOPE_ROOT, NEWHOPE_Q)

    debug("Computing ahat_shat")
    ahat_shat = Poly_mul(a_hat, s_hat)

    debug("Computing b_hat = a_hat dot s_hat + e_hat")
    b_hat = Poly_add(ahat_shat, e_hat)

    debug("Computing public key pk")
    pk = EncodePK(b_hat, publicseed)

    debug("Computing secret key sk")
    sk = EncodePoly(s_hat)

    debug("Public key generation complete. Returning keys")

    return pk, sk

# Encrypts a message and returns a ciphertext
def Encrypt(pk, m, coin):
    print("========================== Encrypting Message ==========================")
    b_hat, publicseed = DecodePK(pk)
    a_hat = GenA(publicseed)

    s_prime = Sample(coin, 0)
    e_prime = Sample(coin, 1)
    e_prime_prime = Sample(coin, 2)

    t_hat = NTT(s_prime, NEWHOPE_ROOT, NEWHOPE_Q)
    e_prime_ntt = NTT(e_prime, NEWHOPE_ROOT, NEWHOPE_Q)

    ahat_that = Poly_mul(a_hat, t_hat)
    u_hat = Poly_add(ahat_that, e_prime_ntt)

    v = EncodeMsg(m)

    bhat_that = Poly_mul(b_hat, t_hat)
    ntt_temp = INTT(bhat_that, NEWHOPE_ROOT, NEWHOPE_Q)

    sum1 = Poly_add(ntt_temp, e_prime_prime)
    v_prime = Poly_add(sum1, v)
    h = Compress(v_prime)
    c = EncodeC(u_hat, h)
    return c

# Decrypts a ciphertext
def Decrypt(c, sk):
    print("========================== Decrypting Message ==========================")
    u_hat, h = DecodeC(c)
    s_hat = DecodePoly(sk)
    v_prime = Decompress(h)

    us_product = Poly_mul(u_hat, s_hat)
    inv_product = INTT(us_product, NEWHOPE_ROOT, NEWHOPE_Q)
    v_sub = PolySubtract(v_prime, inv_product)
    m = DecodeMsg(v_sub)
    return m

# Driver for key creation, encryption and decryption
def main():
    print("=============================================================================")
    print("========================== Starting PKE generation ==========================")
    print("=============================================================================")

    pk, sk = PKEGen()
    coin = os.urandom(32)
    m = [225, 235, 49, 214, 170, 104, 167, 11, 44, 191, 245, 93, 225, 169, 110, 109, 210, 245, 50, 76, 61, 222, 120, 169, 152, 103, 251, 147, 188, 248, 161, 144]
    c = Encrypt(pk, m, coin)
    m_prime = Decrypt(c, sk)
    print("========================== Here is the original message and recovered message ==========================")
    print(m)
    print(m_prime)


if __name__ == "__main__":
    if len(sys.argv) == 2:
        if str(sys.argv[1]).lower() == "debug":
            logging.basicConfig(stream=sys.stdout, level=logging.DEBUG)
