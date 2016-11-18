## serpent.py - pure Python implementation of the Serpent algorithm.
## Bjorn Edstrom <be@bjrn.se> 13 december 2007.
##
## Copyrights
## ==========
##
## This code is a derived from an implementation by Dr Brian Gladman
## (gladman@seven77.demon.co.uk) which is subject to the following license.
## This Python implementation is not subject to any other license.
##
##/* This is an independent implementation of the encryption algorithm:
## *
## * Serpent by Ross Anderson, Eli Biham and Lars Knudsen
## *
## * which is a candidate algorithm in the Advanced Encryption Standard
## * programme of the US National Institute of Standards and Technology
## *
## * Copyright in this implementation is held by Dr B R Gladman but I
## * hereby give permission for its free direct or derivative use subject
## * to acknowledgment of its origin and compliance with any conditions
## * that the originators of the algorithm place on its exploitation.
## *
## * Dr Brian Gladman (gladman@seven77.demon.co.uk) 14th January 1999
## */
##
## The above copyright notice must not be removed.
##
## Information
## ===========
##
## Anyone thinking of using this code should reconsider. It's slow.
## Try python-mcrypt instead. In case a faster library is not installed
## on the target system, this code can be used as a portable fallback.

try:
    import psyco
    psyco.full()
except ImportError:
    pass

block_size = 16
key_size = 32

class Serpent:

    def __init__(self, key=None):
        """Serpent."""

        if key:
            self.set_key(key)


    def set_key(self, key):
        """Init."""

        key_len = len(key)
        if key_len % 4:
            # XXX: add padding?
            raise KeyError("key not a multiple of 4")
        if key_len > 32:
            # XXX: prune?
            raise KeyError("key_len > 32")

        self.key_context = [0] * 140

        key_word32 = [0] * 32
        i = 0
        while key:
            key_word32[i] = struct.unpack("<L", key[0:4])[0]
            key = key[4:]
            i += 1

        set_key(self.key_context, key_word32, key_len)


    def decrypt(self, block):
        """Decrypt blocks."""

        if len(block) % 16:
            raise ValueError("block size must be a multiple of 16")

        plaintext = b''

        while block:
            a, b, c, d = struct.unpack("<4L", block[:16])
            temp = [a, b, c, d]
            decrypt(self.key_context, temp)
            plaintext += struct.pack("<4L", *temp)
            block = block[16:]

        return plaintext


    def encrypt(self, block):
        """Encrypt blocks."""

        if len(block) % 16:
            raise ValueError("block size must be a multiple of 16")

        ciphertext = b''

        while block:
            a, b, c, d = struct.unpack("<4L", block[0:16])
            temp = [a, b, c, d]
            encrypt(self.key_context, temp)
            ciphertext += struct.pack("<4L", *temp)
            block = block[16:]

        return ciphertext


    def get_name(self):
        """Return the name of the cipher."""

        return "Serpent"


    def get_block_size(self):
        """Get cipher block size in bytes."""

        return 16


    def get_key_size(self):
        """Get cipher key size in bytes."""

        return 32


#
# Private.
#

import struct
import sys

WORD_BIGENDIAN = 0
if sys.byteorder == 'big':
    WORD_BIGENDIAN = 1

def rotr32(x, n):
    return (x >> n) | ((x << (32 - n)) & 0xFFFFFFFF)

def rotl32(x, n):
    return ((x << n) & 0xFFFFFFFF) | (x >> (32 - n))

def byteswap32(x):
    return ((x & 0xff) << 24) | (((x >> 8) & 0xff) << 16) | \
           (((x >> 16) & 0xff) << 8) | ((x >> 24) & 0xff)

def sb0(a, b, c, d, e, f, g, h):
    t1 = a ^ d
    t2 = a & d
    t3 = c ^ t1
    t6 = b & t1
    t4 = b ^ t3
    t10 = (~t3) % 0x100000000
    h = t2 ^ t4
    t7 = a ^ t6
    t14 = (~t7) % 0x100000000
    t8 = c | t7
    t11 = t3 ^ t7
    g = t4 ^ t8
    t12 = h & t11
    f = t10 ^ t12
    e = t12 ^ t14
    return e, f, g, h

def ib0(a, b, c, d, e, f, g, h):
    t1 = (~a) % 0x100000000
    t2 = a ^ b
    t3 = t1 | t2
    t4 = d ^ t3
    t7 = d & t2
    t5 = c ^ t4
    t8 = t1 ^ t7
    g = t2 ^ t5
    t11 = a & t4
    t9 = g & t8
    t14 = t5 ^ t8
    f = t4 ^ t9
    t12 = t5 | f
    h = t11 ^ t12
    e = h ^ t14
    return e, f, g, h

def sb1(a, b, c, d, e, f, g, h):
    t1 = (~a) % 0x100000000
    t2 = b ^ t1
    t3 = a | t2
    t4 = d | t2
    t5 = c ^ t3
    g = d ^ t5
    t7 = b ^ t4
    t8 = t2 ^ g
    t9 = t5 & t7
    h = t8 ^ t9
    t11 = t5 ^ t7
    f = h ^ t11
    t13 = t8 & t11
    e = t5 ^ t13
    return e, f, g, h

def ib1(a, b, c, d, e, f, g, h):
    t1 = a ^ d
    t2 = a & b
    t3 = b ^ c
    t4 = a ^ t3
    t5 = b | d
    t7 = c | t1
    h = t4 ^ t5
    t8 = b ^ t7
    t11 = (~t2) % 0x100000000
    t9 = t4 & t8
    f = t1 ^ t9
    t13 = t9 ^ t11
    t12 = h & f
    g = t12 ^ t13
    t15 = a & d
    t16 = c ^ t13
    e = t15 ^ t16
    return e, f, g, h

def sb2(a, b, c, d, e, f, g, h):
    t1 = (~a) % 0x100000000
    t2 = b ^ d
    t3 = c & t1
    t13 = d | t1
    e = t2 ^ t3
    t5 = c ^ t1
    t6 = c ^ e
    t7 = b & t6
    t10 = e | t5
    h = t5 ^ t7
    t9 = d | t7
    t11 = t9 & t10
    t14 = t2 ^ h
    g = a ^ t11
    t15 = g ^ t13
    f = t14 ^ t15
    return e, f, g, h

def ib2(a, b, c, d, e, f, g, h):
    t1 = b ^ d
    t2 = (~t1) % 0x100000000
    t3 = a ^ c
    t4 = c ^ t1
    t7 = a | t2
    t5 = b & t4
    t8 = d ^ t7
    t11 = (~t4) % 0x100000000
    e = t3 ^ t5
    t9 = t3 | t8
    t14 = d & t11
    h = t1 ^ t9
    t12 = e | h
    f = t11 ^ t12
    t15 = t3 ^ t12
    g = t14 ^ t15
    return e, f, g, h

def sb3(a, b, c, d, e, f, g, h):
    t1 = a ^ c
    t2 = d ^ t1
    t3 = a & t2
    t4 = d ^ t3
    t5 = b & t4
    g = t2 ^ t5
    t7 = a | g
    t8 = b | d
    t11 = a | d
    t9 = t4 & t7
    f = t8 ^ t9
    t12 = b ^ t11
    t13 = g ^ t9
    t15 = t3 ^ t8
    h = t12 ^ t13
    t16 = c & t15
    e = t12 ^ t16
    return e, f, g, h

def ib3(a, b, c, d, e, f, g, h):
    t1 = b ^ c
    t2 = b | c
    t3 = a ^ c
    t7 = a ^ d
    t4 = t2 ^ t3
    t5 = d | t4
    t9 = t2 ^ t7
    e = t1 ^ t5
    t8 = t1 | t5
    t11 = a & t4
    g = t8 ^ t9
    t12 = e | t9
    f = t11 ^ t12
    t14 = a & g
    t15 = t2 ^ t14
    t16 = e & t15
    h = t4 ^ t16
    return e, f, g, h

def sb4(a, b, c, d, e, f, g, h):
    t1 = a ^ d
    t2 = d & t1
    t3 = c ^ t2
    t4 = b | t3
    h = t1 ^ t4
    t6 = (~b) % 0x100000000
    t7 = t1 | t6
    e = t3 ^ t7
    t9 = a & e
    t10 = t1 ^ t6
    t11 = t4 & t10
    g = t9 ^ t11
    t13 = a ^ t3
    t14 = t10 & g
    f = t13 ^ t14
    return e, f, g, h

def ib4(a, b, c, d, e, f, g, h):
    t1 = c ^ d
    t2 = c | d
    t3 = b ^ t2
    t4 = a & t3
    f = t1 ^ t4
    t6 = a ^ d
    t7 = b | d
    t8 = t6 & t7
    h = t3 ^ t8
    t10 = (~a) % 0x100000000
    t11 = c ^ h
    t12 = t10 | t11
    e = t3 ^ t12
    t14 = c | t4
    t15 = t7 ^ t14
    t16 = h | t10
    g = t15 ^ t16
    return e, f, g, h

def sb5(a, b, c, d, e, f, g, h):
    t1 = (~a) % 0x100000000
    t2 = a ^ b
    t3 = a ^ d
    t4 = c ^ t1
    t5 = t2 | t3
    e = t4 ^ t5
    t7 = d & e
    t8 = t2 ^ e
    t10 = t1 | e
    f = t7 ^ t8
    t11 = t2 | t7
    t12 = t3 ^ t10
    t14 = b ^ t7
    g = t11 ^ t12
    t15 = f & t12
    h = t14 ^ t15
    return e, f, g, h

def ib5(a, b, c, d, e, f, g, h):
    t1 = (~c) % 0x100000000
    t2 = b & t1
    t3 = d ^ t2
    t4 = a & t3
    t5 = b ^ t1
    h = t4 ^ t5
    t7 = b | h
    t8 = a & t7
    f = t3 ^ t8
    t10 = a | d
    t11 = t1 ^ t7
    e = t10 ^ t11
    t13 = a ^ c
    t14 = b & t10
    t15 = t4 | t13
    g = t14 ^ t15
    return e, f, g, h

def sb6(a, b, c, d, e, f, g, h):
    t1 = (~a) % 0x100000000
    t2 = a ^ d
    t3 = b ^ t2
    t4 = t1 | t2
    t5 = c ^ t4
    f = b ^ t5
    t13 = (~t5) % 0x100000000
    t7 = t2 | f
    t8 = d ^ t7
    t9 = t5 & t8
    g = t3 ^ t9
    t11 = t5 ^ t8
    e = g ^ t11
    t14 = t3 & t11
    h = t13 ^ t14
    return e, f, g, h

def ib6(a, b, c, d, e, f, g, h):
    t1 = (~a) % 0x100000000
    t2 = a ^ b
    t3 = c ^ t2
    t4 = c | t1
    t5 = d ^ t4
    t13 = d & t1
    f = t3 ^ t5
    t7 = t3 & t5
    t8 = t2 ^ t7
    t9 = b | t8
    h = t5 ^ t9
    t11 = b | h
    e = t8 ^ t11
    t14 = t3 ^ t11
    g = t13 ^ t14
    return e, f, g, h

def sb7(a, b, c, d, e, f, g, h):
    t1 = (~c) % 0x100000000
    t2 = b ^ c
    t3 = b | t1
    t4 = d ^ t3
    t5 = a & t4
    t7 = a ^ d
    h = t2 ^ t5
    t8 = b ^ t5
    t9 = t2 | t8
    t11 = d & t3
    f = t7 ^ t9
    t12 = t5 ^ f
    t15 = t1 | t4
    t13 = h & t12
    g = t11 ^ t13
    t16 = t12 ^ g
    e = t15 ^ t16
    return e, f, g, h

def ib7(a, b, c, d, e, f, g, h):
    t1 = a & b
    t2 = a | b
    t3 = c | t1
    t4 = d & t2
    h = t3 ^ t4
    t6 = (~d) % 0x100000000
    t7 = b ^ t4
    t8 = h ^ t6
    t11 = c ^ t7
    t9 = t7 | t8
    f = a ^ t9
    t12 = d | f
    e = t11 ^ t12
    t14 = a & h
    t15 = t3 ^ f
    t16 = e ^ t14
    g = t15 ^ t16
    return e, f, g, h

def k_xor(key, r, a, b, c, d):
    a ^= key[4 * r +  8]
    b ^= key[4 * r +  9]
    c ^= key[4 * r + 10]
    d ^= key[4 * r + 11]
    return a, b, c, d

def k_set(key, r):
    a = key[4 * r +  8]
    b = key[4 * r +  9]
    c = key[4 * r + 10]
    d = key[4 * r + 11]
    return a, b, c, d

def k_get(key, r, a, b, c, d):
    key[4 * r +  8] = a
    key[4 * r +  9] = b
    key[4 * r + 10] = c
    key[4 * r + 11] = d

def rot(a, b, c, d):
    a = rotl32(a, 13)
    c = rotl32(c, 3)
    d ^= c ^ ((a << 3) & 0xFFFFFFFF)
    b ^= a ^ c
    d = rotl32(d, 7)
    b = rotl32(b, 1)
    a ^= b ^ d
    c ^= d ^ ((b << 7) & 0xFFFFFFFF)
    a = rotl32(a, 5)
    c = rotl32(c, 22)
    return a, b, c, d

def irot(a, b, c, d):
    c = rotr32(c, 22)
    a = rotr32(a, 5)
    c ^= d ^ ((b << 7) & 0xFFFFFFFF)
    a ^= b ^ d
    d = rotr32(d, 7)
    b = rotr32(b, 1)
    d ^= c ^ ((a << 3) & 0xFFFFFFFF)
    b ^= a ^ c
    c = rotr32(c, 3)
    a = rotr32(a, 13)
    return a, b, c, d

def set_key(l_key, key, key_len):
    key_len *= 8
    if key_len > 256:
        return False

    i = 0
    lk = (key_len + 31) // 32
    while i < lk:
        l_key[i] = key[i]
        if WORD_BIGENDIAN:
            l_key[i] = byteswap32(key[i])
        i += 1

    if key_len < 256:
        while i < 8:
            l_key[i] = 0
            i += 1
        i = key_len // 32
        lk = 1 << (key_len % 32)
        l_key[i] = (l_key[i] & (lk - 1)) | lk
    for i in range(132):
        lk = l_key[i] ^ l_key[i + 3] ^ l_key[i + 5] ^ l_key[i + 7] ^ 0x9e3779b9 ^ i
        l_key[i + 8] = ((lk << 11) & 0xFFFFFFFF) | (lk >> 21)

    key = l_key
    e = 0
    f = 0
    g = 0
    h = 0
    a, b, c, d = k_set(key,  0); e, f, g, h = sb3(a, b, c, d, e, f, g, h); k_get(key,  0, e, f, g, h)
    a, b, c, d = k_set(key,  1); e, f, g, h = sb2(a, b, c, d, e, f, g, h); k_get(key,  1, e, f, g, h)
    a, b, c, d = k_set(key,  2); e, f, g, h = sb1(a, b, c, d, e, f, g, h); k_get(key,  2, e, f, g, h)
    a, b, c, d = k_set(key,  3); e, f, g, h = sb0(a, b, c, d, e, f, g, h); k_get(key,  3, e, f, g, h)
    a, b, c, d = k_set(key,  4); e, f, g, h = sb7(a, b, c, d, e, f, g, h); k_get(key,  4, e, f, g, h)
    a, b, c, d = k_set(key,  5); e, f, g, h = sb6(a, b, c, d, e, f, g, h); k_get(key,  5, e, f, g, h)
    a, b, c, d = k_set(key,  6); e, f, g, h = sb5(a, b, c, d, e, f, g, h); k_get(key,  6, e, f, g, h)
    a, b, c, d = k_set(key,  7); e, f, g, h = sb4(a, b, c, d, e, f, g, h); k_get(key,  7, e, f, g, h)
    a, b, c, d = k_set(key,  8); e, f, g, h = sb3(a, b, c, d, e, f, g, h); k_get(key,  8, e, f, g, h)
    a, b, c, d = k_set(key,  9); e, f, g, h = sb2(a, b, c, d, e, f, g, h); k_get(key,  9, e, f, g, h)
    a, b, c, d = k_set(key, 10); e, f, g, h = sb1(a, b, c, d, e, f, g, h); k_get(key, 10, e, f, g, h)
    a, b, c, d = k_set(key, 11); e, f, g, h = sb0(a, b, c, d, e, f, g, h); k_get(key, 11, e, f, g, h)
    a, b, c, d = k_set(key, 12); e, f, g, h = sb7(a, b, c, d, e, f, g, h); k_get(key, 12, e, f, g, h)
    a, b, c, d = k_set(key, 13); e, f, g, h = sb6(a, b, c, d, e, f, g, h); k_get(key, 13, e, f, g, h)
    a, b, c, d = k_set(key, 14); e, f, g, h = sb5(a, b, c, d, e, f, g, h); k_get(key, 14, e, f, g, h)
    a, b, c, d = k_set(key, 15); e, f, g, h = sb4(a, b, c, d, e, f, g, h); k_get(key, 15, e, f, g, h)
    a, b, c, d = k_set(key, 16); e, f, g, h = sb3(a, b, c, d, e, f, g, h); k_get(key, 16, e, f, g, h)
    a, b, c, d = k_set(key, 17); e, f, g, h = sb2(a, b, c, d, e, f, g, h); k_get(key, 17, e, f, g, h)
    a, b, c, d = k_set(key, 18); e, f, g, h = sb1(a, b, c, d, e, f, g, h); k_get(key, 18, e, f, g, h)
    a, b, c, d = k_set(key, 19); e, f, g, h = sb0(a, b, c, d, e, f, g, h); k_get(key, 19, e, f, g, h)
    a, b, c, d = k_set(key, 20); e, f, g, h = sb7(a, b, c, d, e, f, g, h); k_get(key, 20, e, f, g, h)
    a, b, c, d = k_set(key, 21); e, f, g, h = sb6(a, b, c, d, e, f, g, h); k_get(key, 21, e, f, g, h)
    a, b, c, d = k_set(key, 22); e, f, g, h = sb5(a, b, c, d, e, f, g, h); k_get(key, 22, e, f, g, h)
    a, b, c, d = k_set(key, 23); e, f, g, h = sb4(a, b, c, d, e, f, g, h); k_get(key, 23, e, f, g, h)
    a, b, c, d = k_set(key, 24); e, f, g, h = sb3(a, b, c, d, e, f, g, h); k_get(key, 24, e, f, g, h)
    a, b, c, d = k_set(key, 25); e, f, g, h = sb2(a, b, c, d, e, f, g, h); k_get(key, 25, e, f, g, h)
    a, b, c, d = k_set(key, 26); e, f, g, h = sb1(a, b, c, d, e, f, g, h); k_get(key, 26, e, f, g, h)
    a, b, c, d = k_set(key, 27); e, f, g, h = sb0(a, b, c, d, e, f, g, h); k_get(key, 27, e, f, g, h)
    a, b, c, d = k_set(key, 28); e, f, g, h = sb7(a, b, c, d, e, f, g, h); k_get(key, 28, e, f, g, h)
    a, b, c, d = k_set(key, 29); e, f, g, h = sb6(a, b, c, d, e, f, g, h); k_get(key, 29, e, f, g, h)
    a, b, c, d = k_set(key, 30); e, f, g, h = sb5(a, b, c, d, e, f, g, h); k_get(key, 30, e, f, g, h)
    a, b, c, d = k_set(key, 31); e, f, g, h = sb4(a, b, c, d, e, f, g, h); k_get(key, 31, e, f, g, h)
    a, b, c, d = k_set(key, 32); e, f, g, h = sb3(a, b, c, d, e, f, g, h); k_get(key, 32, e, f, g, h)

def encrypt(key, in_blk):
    a = in_blk[0]
    b = in_blk[1]
    c = in_blk[2]
    d = in_blk[3]
    if WORD_BIGENDIAN:
        a = byteswap32(a)
        b = byteswap32(b)
        c = byteswap32(c)
        d = byteswap32(d)
    e = 0
    f = 0
    g = 0
    h = 0
    a, b, c, d = k_xor(key,  0, a, b, c, d); e, f, g, h = sb0(a, b, c, d, e, f, g, h); e, f, g, h = rot(e, f, g, h)
    e, f, g, h = k_xor(key,  1, e, f, g, h); a, b, c, d = sb1(e, f, g, h, a, b, c, d); a, b, c, d = rot(a, b, c, d)
    a, b, c, d = k_xor(key,  2, a, b, c, d); e, f, g, h = sb2(a, b, c, d, e, f, g, h); e, f, g, h = rot(e, f, g, h)
    e, f, g, h = k_xor(key,  3, e, f, g, h); a, b, c, d = sb3(e, f, g, h, a, b, c, d); a, b, c, d = rot(a, b, c, d)
    a, b, c, d = k_xor(key,  4, a, b, c, d); e, f, g, h = sb4(a, b, c, d, e, f, g, h); e, f, g, h = rot(e, f, g, h)
    e, f, g, h = k_xor(key,  5, e, f, g, h); a, b, c, d = sb5(e, f, g, h, a, b, c, d); a, b, c, d = rot(a, b, c, d)
    a, b, c, d = k_xor(key,  6, a, b, c, d); e, f, g, h = sb6(a, b, c, d, e, f, g, h); e, f, g, h = rot(e, f, g, h)
    e, f, g, h = k_xor(key,  7, e, f, g, h); a, b, c, d = sb7(e, f, g, h, a, b, c, d); a, b, c, d = rot(a, b, c, d)
    a, b, c, d = k_xor(key,  8, a, b, c, d); e, f, g, h = sb0(a, b, c, d, e, f, g, h); e, f, g, h = rot(e, f, g, h)
    e, f, g, h = k_xor(key,  9, e, f, g, h); a, b, c, d = sb1(e, f, g, h, a, b, c, d); a, b, c, d = rot(a, b, c, d)
    a, b, c, d = k_xor(key, 10, a, b, c, d); e, f, g, h = sb2(a, b, c, d, e, f, g, h); e, f, g, h = rot(e, f, g, h)
    e, f, g, h = k_xor(key, 11, e, f, g, h); a, b, c, d = sb3(e, f, g, h, a, b, c, d); a, b, c, d = rot(a, b, c, d)
    a, b, c, d = k_xor(key, 12, a, b, c, d); e, f, g, h = sb4(a, b, c, d, e, f, g, h); e, f, g, h = rot(e, f, g, h)
    e, f, g, h = k_xor(key, 13, e, f, g, h); a, b, c, d = sb5(e, f, g, h, a, b, c, d); a, b, c, d = rot(a, b, c, d)
    a, b, c, d = k_xor(key, 14, a, b, c, d); e, f, g, h = sb6(a, b, c, d, e, f, g, h); e, f, g, h = rot(e, f, g, h)
    e, f, g, h = k_xor(key, 15, e, f, g, h); a, b, c, d = sb7(e, f, g, h, a, b, c, d); a, b, c, d = rot(a, b, c, d)
    a, b, c, d = k_xor(key, 16, a, b, c, d); e, f, g, h = sb0(a, b, c, d, e, f, g, h); e, f, g, h = rot(e, f, g, h)
    e, f, g, h = k_xor(key, 17, e, f, g, h); a, b, c, d = sb1(e, f, g, h, a, b, c, d); a, b, c, d = rot(a, b, c, d)
    a, b, c, d = k_xor(key, 18, a, b, c, d); e, f, g, h = sb2(a, b, c, d, e, f, g, h); e, f, g, h = rot(e, f, g, h)
    e, f, g, h = k_xor(key, 19, e, f, g, h); a, b, c, d = sb3(e, f, g, h, a, b, c, d); a, b, c, d = rot(a, b, c, d)
    a, b, c, d = k_xor(key, 20, a, b, c, d); e, f, g, h = sb4(a, b, c, d, e, f, g, h); e, f, g, h = rot(e, f, g, h)
    e, f, g, h = k_xor(key, 21, e, f, g, h); a, b, c, d = sb5(e, f, g, h, a, b, c, d); a, b, c, d = rot(a, b, c, d)
    a, b, c, d = k_xor(key, 22, a, b, c, d); e, f, g, h = sb6(a, b, c, d, e, f, g, h); e, f, g, h = rot(e, f, g, h)
    e, f, g, h = k_xor(key, 23, e, f, g, h); a, b, c, d = sb7(e, f, g, h, a, b, c, d); a, b, c, d = rot(a, b, c, d)
    a, b, c, d = k_xor(key, 24, a, b, c, d); e, f, g, h = sb0(a, b, c, d, e, f, g, h); e, f, g, h = rot(e, f, g, h)
    e, f, g, h = k_xor(key, 25, e, f, g, h); a, b, c, d = sb1(e, f, g, h, a, b, c, d); a, b, c, d = rot(a, b, c, d)
    a, b, c, d = k_xor(key, 26, a, b, c, d); e, f, g, h = sb2(a, b, c, d, e, f, g, h); e, f, g, h = rot(e, f, g, h)
    e, f, g, h = k_xor(key, 27, e, f, g, h); a, b, c, d = sb3(e, f, g, h, a, b, c, d); a, b, c, d = rot(a, b, c, d)
    a, b, c, d = k_xor(key, 28, a, b, c, d); e, f, g, h = sb4(a, b, c, d, e, f, g, h); e, f, g, h = rot(e, f, g, h)
    e, f, g, h = k_xor(key, 29, e, f, g, h); a, b, c, d = sb5(e, f, g, h, a, b, c, d); a, b, c, d = rot(a, b, c, d)
    a, b, c, d = k_xor(key, 30, a, b, c, d); e, f, g, h = sb6(a, b, c, d, e, f, g, h); e, f, g, h = rot(e, f, g, h)
    e, f, g, h = k_xor(key, 31, e, f, g, h); a, b, c, d = sb7(e, f, g, h, a, b, c, d)
    a, b, c, d = k_xor(key, 32, a, b, c, d)
    if WORD_BIGENDIAN:
        a = byteswap32(a)
        b = byteswap32(b)
        c = byteswap32(c)
        d = byteswap32(d)
    in_blk[0] = a
    in_blk[1] = b
    in_blk[2] = c
    in_blk[3] = d

def decrypt(key, in_blk):
    a = in_blk[0]
    b = in_blk[1]
    c = in_blk[2]
    d = in_blk[3]
    if WORD_BIGENDIAN:
        a = byteswap32(a)
        b = byteswap32(b)
        c = byteswap32(c)
        d = byteswap32(d)
    e = 0
    f = 0
    g = 0
    h = 0
    a, b, c, d = k_xor(key, 32, a, b, c, d);                                e, f, g, h = ib7(a, b, c, d, e, f, g, h)
    e, f, g, h = k_xor(key, 31, e, f, g, h); e, f, g, h = irot(e, f, g, h); a, b, c, d = ib6(e, f, g, h, a, b, c, d)
    a, b, c, d = k_xor(key, 30, a, b, c, d); a, b, c, d = irot(a, b, c, d); e, f, g, h = ib5(a, b, c, d, e, f, g, h)
    e, f, g, h = k_xor(key, 29, e, f, g, h); e, f, g, h = irot(e, f, g, h); a, b, c, d = ib4(e, f, g, h, a, b, c, d)
    a, b, c, d = k_xor(key, 28, a, b, c, d); a, b, c, d = irot(a, b, c, d); e, f, g, h = ib3(a, b, c, d, e, f, g, h)
    e, f, g, h = k_xor(key, 27, e, f, g, h); e, f, g, h = irot(e, f, g, h); a, b, c, d = ib2(e, f, g, h, a, b, c, d)
    a, b, c, d = k_xor(key, 26, a, b, c, d); a, b, c, d = irot(a, b, c, d); e, f, g, h = ib1(a, b, c, d, e, f, g, h)
    e, f, g, h = k_xor(key, 25, e, f, g, h); e, f, g, h = irot(e, f, g, h); a, b, c, d = ib0(e, f, g, h, a, b, c, d)
    a, b, c, d = k_xor(key, 24, a, b, c, d); a, b, c, d = irot(a, b, c, d); e, f, g, h = ib7(a, b, c, d, e, f, g, h)
    e, f, g, h = k_xor(key, 23, e, f, g, h); e, f, g, h = irot(e, f, g, h); a, b, c, d = ib6(e, f, g, h, a, b, c, d)
    a, b, c, d = k_xor(key, 22, a, b, c, d); a, b, c, d = irot(a, b, c, d); e, f, g, h = ib5(a, b, c, d, e, f, g, h)
    e, f, g, h = k_xor(key, 21, e, f, g, h); e, f, g, h = irot(e, f, g, h); a, b, c, d = ib4(e, f, g, h, a, b, c, d)
    a, b, c, d = k_xor(key, 20, a, b, c, d); a, b, c, d = irot(a, b, c, d); e, f, g, h = ib3(a, b, c, d, e, f, g, h)
    e, f, g, h = k_xor(key, 19, e, f, g, h); e, f, g, h = irot(e, f, g, h); a, b, c, d = ib2(e, f, g, h, a, b, c, d)
    a, b, c, d = k_xor(key, 18, a, b, c, d); a, b, c, d = irot(a, b, c, d); e, f, g, h = ib1(a, b, c, d, e, f, g, h)
    e, f, g, h = k_xor(key, 17, e, f, g, h); e, f, g, h = irot(e, f, g, h); a, b, c, d = ib0(e, f, g, h, a, b, c, d)
    a, b, c, d = k_xor(key, 16, a, b, c, d); a, b, c, d = irot(a, b, c, d); e, f, g, h = ib7(a, b, c, d, e, f, g, h)
    e, f, g, h = k_xor(key, 15, e, f, g, h); e, f, g, h = irot(e, f, g, h); a, b, c, d = ib6(e, f, g, h, a, b, c, d)
    a, b, c, d = k_xor(key, 14, a, b, c, d); a, b, c, d = irot(a, b, c, d); e, f, g, h = ib5(a, b, c, d, e, f, g, h)
    e, f, g, h = k_xor(key, 13, e, f, g, h); e, f, g, h = irot(e, f, g, h); a, b, c, d = ib4(e, f, g, h, a, b, c, d)
    a, b, c, d = k_xor(key, 12, a, b, c, d); a, b, c, d = irot(a, b, c, d); e, f, g, h = ib3(a, b, c, d, e, f, g, h)
    e, f, g, h = k_xor(key, 11, e, f, g, h); e, f, g, h = irot(e, f, g, h); a, b, c, d = ib2(e, f, g, h, a, b, c, d)
    a, b, c, d = k_xor(key, 10, a, b, c, d); a, b, c, d = irot(a, b, c, d); e, f, g, h = ib1(a, b, c, d, e, f, g, h)
    e, f, g, h = k_xor(key,  9, e, f, g, h); e, f, g, h = irot(e, f, g, h); a, b, c, d = ib0(e, f, g, h, a, b, c, d)
    a, b, c, d = k_xor(key,  8, a, b, c, d); a, b, c, d = irot(a, b, c, d); e, f, g, h = ib7(a, b, c, d, e, f, g, h)
    e, f, g, h = k_xor(key,  7, e, f, g, h); e, f, g, h = irot(e, f, g, h); a, b, c, d = ib6(e, f, g, h, a, b, c, d)
    a, b, c, d = k_xor(key,  6, a, b, c, d); a, b, c, d = irot(a, b, c, d); e, f, g, h = ib5(a, b, c, d, e, f, g, h)
    e, f, g, h = k_xor(key,  5, e, f, g, h); e, f, g, h = irot(e, f, g, h); a, b, c, d = ib4(e, f, g, h, a, b, c, d)
    a, b, c, d = k_xor(key,  4, a, b, c, d); a, b, c, d = irot(a, b, c, d); e, f, g, h = ib3(a, b, c, d, e, f, g, h)
    e, f, g, h = k_xor(key,  3, e, f, g, h); e, f, g, h = irot(e, f, g, h); a, b, c, d = ib2(e, f, g, h, a, b, c, d)
    a, b, c, d = k_xor(key,  2, a, b, c, d); a, b, c, d = irot(a, b, c, d); e, f, g, h = ib1(a, b, c, d, e, f, g, h)
    e, f, g, h = k_xor(key,  1, e, f, g, h); e, f, g, h = irot(e, f, g, h); a, b, c, d = ib0(e, f, g, h, a, b, c, d)
    a, b, c, d = k_xor(key,  0, a, b, c, d)
    if WORD_BIGENDIAN:
        a = byteswap32(a)
        b = byteswap32(b)
        c = byteswap32(c)
        d = byteswap32(d)
    in_blk[0] = a
    in_blk[1] = b
    in_blk[2] = c
    in_blk[3] = d

__testkey = b'\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f'
__testdat = b'\x00\x01\x02\x03\x04\x05\x06\x07\x08\t\n\x0b\x0c\r\x0e\x0f'
assert b'\xde&\x9f\xf83\xe42\xb8[.\x88\xd2p\x1c\xe7\\' == Serpent(__testkey).encrypt(__testdat)
assert __testdat == Serpent(__testkey).decrypt(b'\xde&\x9f\xf83\xe42\xb8[.\x88\xd2p\x1c\xe7\\')
