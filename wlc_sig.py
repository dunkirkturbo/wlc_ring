#!/usr/bin/env python
# coding: utf-8

import secrets
import time
from Crypto.Hash import SHA256
from Crypto.Util.number import *
from tqdm import tqdm
from fastecdsa import keys, curve, point
from hashlib import sha256

# define basic parameter
my_curve = curve.P256
curve_size = 256 // 8
g = my_curve.G
p = my_curve.q
generator_u = g * secrets.randbelow(p)


# define basic operation
# int(c, 16) is to convert hexadecmical strings to actual numbers, I don't think it would limit the size of the number
def A(r):
    return g * r
def Z(sk, r, c):
    return (r - c * sk) % p
def V(z, pk, c):
    return (g * z) + (pk * c)
def V1(z):
    return g * z
def V2(pk, c):
    return pk * c


# key generation calling ecc keyGen
def KeyGen():
#     sk is before pk
    return keys.gen_keypair(my_curve)


def pt_to_bytes(point):
    x = long_to_bytes(point.x).rjust(curve_size, b'\x00')
    y = long_to_bytes(point.y).rjust(curve_size, b'\x00')
    return x + y
    
# algorithm 1: Schnorr signature
# not for ring signature
def t_type_sign(m, sk):
    r = secrets.randbelow(p)
    R = A(r)
    concat_str = m.encode() + pt_to_bytes(R)
    c = sha256(concat_str).hexdigest()
    z = Z(sk, r, int(c, 16))
    return z, c

def t_type_vrf(m, pk, sigma):
    z = sigma[0]
    c = sigma[1]
    R_vrf = V(z, pk, int(c, 16))
    concat_str = m.encode() + pt_to_bytes(R_vrf)
    c_vrf = sha256(concat_str).hexdigest()
    if c != c_vrf:
        return 0
    return 1

# def list_to_bytes(l):
#     a = b''
#     for i in range(len(l)):
#         a = a + long_to_bytes(l[i])
#     return a

def ptlist_to_bytes(pl):
    a = b''
    for i in range(len(pl)):
        a = a + pt_to_bytes(pl[i])
    return a
    

# (aos_sign, aos_vrf) is the ring signature scheme of AOS ring signature in Asiacrypt 2002 (Schnorr-based)
# assume PK is an array of public keys pk1, pk2,...,pkn
# j is the location of the pk corresponding to sk; note the list starts at 0 instead of 1
def aos_sign(m, PK, sk, j):
    universal_pk_str = ptlist_to_bytes(PK)

    r = secrets.randbelow(p)
    R_array = [None] * len(PK)
    c_array = [None] * len(PK)
    z_array = [None] * len(PK)
    R_array[j] = A(r)
    for i in range(j + 1, len(PK)):
        concat_str = m.encode() + universal_pk_str + pt_to_bytes(R_array[i - 1])
        c_array[i] = sha256(concat_str).hexdigest()
        z_array[i] = secrets.randbelow(p)
        R_array[i] = V(z_array[i], PK[i], int(c_array[i], 16))
    for i in range(j):
        concat_str = m.encode() + universal_pk_str + pt_to_bytes(R_array[i - 1])
        c_array[i] = sha256(concat_str).hexdigest()
        z_array[i] = secrets.randbelow(p)
        R_array[i] = V(z_array[i], PK[i], int(c_array[i], 16))
    concat_str = m.encode() + universal_pk_str + pt_to_bytes(R_array[j - 1])
    c_array[j] = sha256(concat_str).hexdigest()
    z_array[j] = Z(sk, r, int(c_array[j], 16))
    return (c_array[0], z_array)


def aos_vrf(m, PK, sigma):
    universal_pk_str = ptlist_to_bytes(PK)
    c = sigma[0]
    z_array = sigma[1]
    R_array = [None] * len(PK)
    R_array[0] = V(z_array[0], PK[0], int(c, 16))

    for i in range (1, len(PK)):
        concat_str = m.encode() + universal_pk_str + pt_to_bytes(R_array[i - 1])
        c_i = sha256(concat_str).hexdigest()
        R_array[i] = V(z_array[i], PK[i], int(c_i, 16))
    concat_str = m.encode() + universal_pk_str + pt_to_bytes(R_array[len(PK) - 1])
    c_vrf = sha256(concat_str).hexdigest()
    if c != c_vrf:
        print('AOS signature verification failed')
        return 0
    return 1


def hash_point(pk):
    h = int(sha256(pt_to_bytes(pk)).hexdigest(), 16) % p
    return h * g

# without calling the NISA function, size O(n)
def wlc_basic_sign(M, PK, SK_pi, pi):
    n, m = len(PK), len(PK[pi])
    c_array, s_array = [None] * n, [None] * m
    r_array = [None] * m
    H_array = [[None] * m] * n
    I_array = [None] * m
    L_array, R_array = [None] * m, [None] * m

    for i in range(n):
        for j in range(m):
            H_array[i][j] = hash_point(PK[i][j])
    for j in range(m):
        I_array[j] = inverse(SK_pi[j], p) * H_array[pi][j]  # compute tag for linkable property
        
    for i in range(n):
        if i != pi:
            c_array[i] = secrets.randbelow(p)
    for j in range(m):
        r_array[j] = secrets.randbelow(p)
        L_array[j] = r_array[j] * g
        R_array[j] = r_array[j] * I_array[j]
        for i in range(n):
            if i != pi:
                L_array[j] += V2(PK[i][j], c_array[i])
                R_array[j] += V2(H_array[i][j], c_array[i])
    
    c = int(sha256(M.encode() + ptlist_to_bytes(L_array) + ptlist_to_bytes(R_array)).hexdigest(), 16) % p
    c_array[pi] = 0
    for i in range(n):
        if i != pi:
            c_array[pi] += c_array[i]
    c_array[pi] = (c - c_array[pi]) % p

    for j in range(m):
        s_array[j] = Z(SK_pi[j], r_array[j], c_array[pi])

    return s_array, c_array, I_array

def wlc_basic_vrf(M, PK, sigma):
    s_array = sigma[0]
    c_array = sigma[1]
    I_array = sigma[2]

    n, m = len(PK), len(PK[0])
    H_array = [[None] * m] * n
    L_array, R_array = [None] * m, [None] * m

    for i in range(n):
        for j in range(m):
            H_array[i][j] = hash_point(PK[i][j])
    
    for j in range(m):
        L_array[j] = s_array[j] * g
        R_array[j] = s_array[j] * I_array[j]
        for i in range(n):
            L_array[j] += V2(PK[i][j], c_array[i])
            R_array[j] += V2(H_array[i][j], c_array[i])
    c = 0
    for i in range(n):
        c += c_array[i]
    c %= p
    c_vrf = int(sha256(M.encode() + ptlist_to_bytes(L_array) + ptlist_to_bytes(R_array)).hexdigest(), 16) % p
    if c != c_vrf:
        return 0
    return 1



# Loop in NISA Proof
# u: Hash(P, generator_u, c)
def P_proof(g_list, u, a, b, L, R):
    n = len(a)
    if n == 1:
        return L, R, a, b
    n_half = n // 2
    c_L, c_R = 0, 0
    for i in range(n_half):
        c_L += (a[i] * b[n_half + i]) % p
        c_R += (a[n_half + i] * b[i]) % p
    L_cur, R_cur = u * c_L, u * c_R
    for i in range(n_half):
        L_cur = L_cur + g_list[n_half + i] * a[i]
        R_cur = R_cur + g_list[i] * a[n_half + i]
    L.append(L_cur)
    R.append(R_cur)
    x = int(sha256(pt_to_bytes(L_cur) + pt_to_bytes(R_cur)).hexdigest(), 16)
    x_inv = inverse(x, p)
    g_list_new = [None] * n_half
    b_value = (x_inv * b[0] + x * b[n_half]) % p
    a_new, b_new = [None] * n_half, [b_value] * n_half
    for i in range(n_half):
        g_list_new[i] = x_inv * g_list[i] + x * g_list[n_half + i]
        a_new[i] = x * a[i] + x_inv * a[n_half + i]
        # b_new[i] = x_inv * b[i] + x * b[n_half + i]
    return P_proof(g_list_new, u, a_new, b_new, L, R)

def NISA_proof(g_list, P, c, a):
    concat_str = pt_to_bytes(P) + pt_to_bytes(generator_u) + long_to_bytes(c)
    u = int(sha256(concat_str).hexdigest(), 16) * generator_u
    b = [1] * len(a)
    return P_proof(g_list, u, a, b, [], [])

# helper method to check if i's j-th bit is 1
def check_bit(i, j):
    return (i >> j) & 1

def NISA_vrf(g_list, P, c, NISA_pi):
    L, R, a, b = NISA_pi[0], NISA_pi[1], NISA_pi[2][0], NISA_pi[3][0]
    n, logn = len(g_list), len(L)
    x, x_inv = [None] * logn, [None] * logn
    # y = [0] * len(g_list)
    y = [1] * n
    c %= p
    concat_str = pt_to_bytes(P) + pt_to_bytes(generator_u) + long_to_bytes(c)
    u = int(sha256(concat_str).hexdigest(), 16) * generator_u
    P =  P + u * c
    for j in range(logn):
        x[j] = int(sha256(pt_to_bytes(L[j]) + pt_to_bytes(R[j])).hexdigest(), 16)
        x_inv[j] = inverse(x[j], p)
    for i in range(n):
        for j in range(len(L)):
            if check_bit(i, j) == 1:
                # y[i] += x[j]
                y[i] = (y[i] * x[logn - 1 - j]) % p
            else:
                # y[i] += x_inv[j]
                y[i] = (y[i] * x_inv[logn - 1 - j]) % p 
    check_left = P
    for j in range(logn):
        check_left = check_left + ((x[j] ** 2) % p) * L[j] + ((x_inv[j] ** 2) % p) * R[j]
    check_right = a * b * u
    for i in range(n):
        check_right = check_right + (a * y[i] * g_list[i])
    if check_left == check_right:
        return 1
    return 0
    

def wlc_formal_sign(M, PK, SK_pi, pi):
    n, m = len(PK), len(PK[pi])
    c_array, s_array = [None] * n, [None] * m
    r_array = [None] * m
    H_array = [[None] * m] * n
    I_array = [None] * m
    L_array, R_array = [None] * m, [None] * m

    for i in range(n):
        for j in range(m):
            H_array[i][j] = hash_point(PK[i][j])
    for j in range(m):
        I_array[j] = inverse(SK_pi[j], p) * H_array[pi][j]  # compute tag for linkable property
        
    for i in range(n):
        if i != pi:
            c_array[i] = secrets.randbelow(p)
    for j in range(m):
        r_array[j] = secrets.randbelow(p)
        L_array[j] = r_array[j] * g
        R_array[j] = r_array[j] * I_array[j]
        for i in range(n):
            if i != pi:
                L_array[j] += V2(PK[i][j], c_array[i])
                R_array[j] += V2(H_array[i][j], c_array[i])
    
    c = int(sha256(M.encode() + ptlist_to_bytes(L_array) + ptlist_to_bytes(R_array)).hexdigest(), 16) % p
    c_array[pi] = 0
    for i in range(n):
        if i != pi:
            c_array[pi] += c_array[i]
    c_array[pi] = (c - c_array[pi]) % p

    for j in range(m):
        s_array[j] = Z(SK_pi[j], r_array[j], c_array[pi])

    # compress size to log(n)
    alpha, beta = [None] * m, [None] * m
    g_list = [None] * n
    # P = point.Point(0, 0, curve.P256)
    alpha[0] = int(sha256(M.encode() + pt_to_bytes(L_array[0])).hexdigest(), 16)
    beta[0] = int(sha256(M.encode() + pt_to_bytes(R_array[0])).hexdigest(), 16)
    P = alpha[0] * (L_array[0] - s_array[0] * g) + beta[0] * (R_array[0] - s_array[0] * I_array[0])
    for i in range(n):
        g_list[i] = alpha[0] * PK[i][0] + beta[0] * H_array[i][0]
    for j in range(1, m):
        alpha[j] = int(sha256(M.encode() + pt_to_bytes(L_array[j])).hexdigest(), 16)
        beta[j] = int(sha256(M.encode() + pt_to_bytes(R_array[j])).hexdigest(), 16)
        P += alpha[j] * (L_array[j] - s_array[j] * g)
        P += beta[j] * (R_array[j] - s_array[j] * I_array[j])
        for i in range(n):
            g_list[i] += alpha[j] * PK[i][j] + beta[j] * H_array[i][j]
    NISA_pi = NISA_proof(g_list, P, c, c_array)
    
    return s_array, L_array, R_array, I_array, NISA_pi

def wlc_formal_vrf(M, PK, sigma):
    s_array, L_array, R_array, I_array, NISA_pi = sigma[0], sigma[1], sigma[2], sigma[3], sigma[4]
    n, m = len(PK), len(PK[pi])
    H_array = [[None] * m] * n
    for i in range(n):
        for j in range(m):
            H_array[i][j] = hash_point(PK[i][j])

    alpha, beta = [None] * m, [None] * m
    g_list = [None] * n
    alpha[0] = int(sha256(M.encode() + pt_to_bytes(L_array[0])).hexdigest(), 16)
    beta[0] = int(sha256(M.encode() + pt_to_bytes(R_array[0])).hexdigest(), 16)
    P = alpha[0] * (L_array[0] - s_array[0] * g) + beta[0] * (R_array[0] - s_array[0] * I_array[0])
    for i in range(n):
        g_list[i] = alpha[0] * PK[i][0] + beta[0] * H_array[i][0]
    for j in range(1, m):
        alpha[j] = int(sha256(M.encode() + pt_to_bytes(L_array[j])).hexdigest(), 16)
        beta[j] = int(sha256(M.encode() + pt_to_bytes(R_array[j])).hexdigest(), 16)
        P += alpha[j] * (L_array[j] - s_array[j] * g)
        P += beta[j] * (R_array[j] - s_array[j] * I_array[j])
        for i in range(n):
            g_list[i] += alpha[j] * PK[i][j] + beta[j] * H_array[i][j]

    c = int(sha256(M.encode() + ptlist_to_bytes(L_array) + ptlist_to_bytes(R_array)).hexdigest(), 16) % p
    return NISA_vrf(g_list, P, c, NISA_pi)

if __name__ == '__main__':

    for i in tqdm(range(100)):
        sk, pk = KeyGen()
        s = t_type_sign("F0r_T_Type_t3st1nG", sk)
        if (t_type_vrf("F0r_T_Type_t3st1nG", pk, s) == 0):
            print("failed")
            break
    print("[*] T_type passed")  
    
    PK_num = 20
    for j in tqdm(range(PK_num)):
        PK_set = [None] * PK_num
        for i in range(PK_num):
            _, PK_set[i] = KeyGen()
        sk_j, PK_set[j] = KeyGen()
        s = aos_sign("F0r_AOS_t3st1nG", PK_set, sk_j, j)
        if aos_vrf("F0r_AOS_t3st1nG", PK_set, s) != 1:
            print("failed")
    print("[*] AOS passed")

    m = 10
    SK_pi = [None] * m
    for pi in tqdm(range(PK_num)):
        PK_set = [[None] * m] * PK_num
        for i in range(PK_num):
            for j in range(m):
                _, PK_set[i][j] = KeyGen()
        for j in range(m):
            SK_pi[j], PK_set[pi][j] = KeyGen()
        sigma = wlc_basic_sign("F0r_wlc_basic_t3st1nG", PK_set, SK_pi, pi)
        if wlc_basic_vrf("F0r_wlc_basic_t3st1nG", PK_set, sigma) != 1:
            print("failed")
    print("[*] wlc (without NISA) passed")

    PK_num, m = 20, 50
    time_trail = 1
    PK_set = [[None] * m] * PK_num
    SK_set = [[None] * m] * PK_num
    for i in range(PK_num):
        for j in range(m):
            SK_set[i][j], PK_set[i][j] = KeyGen()
    sign_cost, vrf_cost = 0, 0
    for k in range(time_trail):
        rand_pi = secrets.randbelow(PK_num)
        start_time = time.time()
        sigma = wlc_basic_sign("F0r_wlc_basic_t3st1nG", PK_set, SK_set[rand_pi], rand_pi)
        end_time = time.time()
        sign_cost += (end_time - start_time)
        start_time = time.time()
        wlc_basic_vrf("F0r_wlc_basic_t3st1nG", PK_set, sigma)
        end_time = time.time()
        vrf_cost += (end_time - start_time)
    print('Average sign_cost (n=20, m=50):', sign_cost / time_trail, 's')
    print('Average vrf_cost (n=20, m=50):', vrf_cost / time_trail, 's')

    PK_num = 2**5
    g_list = [None] * PK_num
    c_array = [None] * PK_num
    c = 0
    for i in range(PK_num):
        _, g_list[i] = KeyGen()
        c_array[i] = secrets.randbelow(p)
        c += c_array[i]
    c %= p
    P = c_array[0] * g_list[0]
    for i in range(1, PK_num):
        P += c_array[i] * g_list[i]
    NISA_pi = NISA_proof(g_list, P, c, c_array)
    # NISA_vrf(g_list, P, c, NISA_pi)
    if NISA_vrf(g_list, P, c, NISA_pi) == 1:
        print("[*] NISA(Zero Knowledge Proof) passed")
    else:
        print("failed")

    PK_num, m = 2**5, 20
    SK_pi = [None] * m
    for pi in tqdm(range(PK_num)):
        PK_set = [[None] * m] * PK_num
        for i in range(PK_num):
            for j in range(m):
                _, PK_set[i][j] = KeyGen()
        for j in range(m):
            SK_pi[j], PK_set[pi][j] = KeyGen()
        sigma = wlc_formal_sign("F0r_wlc_formal_t3st1nG", PK_set, SK_pi, pi)
        if wlc_formal_vrf("F0r_wlc_formal_t3st1nG", PK_set, sigma) != 1:
            print("failed")
    print("[*] wlc (with NISA) passed")