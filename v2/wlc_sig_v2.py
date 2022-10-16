from ctypes import *
from Crypto.Util.number import *
from hashlib import sha256
import secrets, time
from tqdm import tqdm

relic = CDLL("./librelic.so")

NIST_256, NIST_P256 = 12, 12
RLC_BN_DIGS = 34
RLC_FP_DIGS = 4
RLC_EP_SIZE = 256 // 8
dig_mask = (1 << 64) - 1

class bn_st(Structure):
    _fields_ = [
        ("alloc", c_int),
        ("used", c_int),
        ("sign", c_int),
        ("dp", (c_ulong * RLC_BN_DIGS))
    ]

# typedef rlc_align uint64_t fp_st[4];
# coord - BASIC(1)
class ep_st(Structure):
    _fields_ = [
        ("x", (c_ulong * RLC_FP_DIGS)),
        ("y", (c_ulong * RLC_FP_DIGS)),
        ("z", (c_ulong * RLC_FP_DIGS)),
        ("coord", c_int)
    ]

relic.core_init()
relic.fp_prime_init()
relic.ep_curve_init()
    
relic.fp_param_set(NIST_256)
relic.ep_param_set(NIST_P256)
relic.fp_param_print()
relic.ep_param_print()

p = bn_st()
relic.ep_curve_get_ord(byref(p))
p_pytype = p.dp[0] + (p.dp[1] << 64) + (p.dp[2] << 128) + (p.dp[3] << 192)
generator_u = ep_st()
relic.ep_curve_get_gen(byref(generator_u))

def pt_to_bytes(point:'ep_st'):
    ep_bin = bytes(point.x) + bytes(point.y) + bytes(point.z)
    return ep_bin

def ptlist_to_bytes(pl):
    a = b''
    for i in range(len(pl)):
        a = a + pt_to_bytes(pl[i])
    return a

def long_to_bn(a_pytype):
    a = bn_st()
    a.alloc = 0
    a.used = 4
    a.sign = 0
    for i in range(4):
        a.dp[i] = (a_pytype >> (i * 64)) & dig_mask
    return a

def bn_mod_inv(a:'bn_st', b:'bn_st'):
    a_inv = bn_st()
    relic.bn_mod_inv(byref(a_inv), pointer(a), pointer(b))
    return a_inv

def bn_rand_mod(a:'bn_st'):
    res = bn_st()
    relic.bn_rand_mod(byref(res), pointer(a))
    return res

def bn_zero():
    res = bn_st()
    relic.bn_zero(byref(res))
    return res

def ep_mul_gen(k:'bn_st'):
    res = ep_st()
    relic.ep_mul_gen(byref(res), pointer(k))
    return res

def ep_mul(k:'bn_st', h:'ep_st'):
    res = ep_st()
    relic.ep_mul_lwnaf(byref(res), pointer(h), pointer(k)) 
    return res

def ep_add(a:'ep_st', b:'ep_st'):
    res = ep_st()
    relic.ep_add_basic(byref(res), pointer(a), pointer(b))
    return res

def ep_sub(a:'ep_st', b:'ep_st'):
    relic.ep_neg(byref(b), pointer(b))
    res = ep_st()
    relic.ep_add_basic(byref(res), pointer(a), pointer(b))
    return res

def fp_sub(a:'bn_st', b:'bn_st'):
    res = bn_st()
    relic.bn_sub(byref(res), pointer(a), pointer(b))
    relic.bn_mod_basic(byref(res), pointer(res), pointer(p))
    return res

def fp_add(a:'bn_st', b:'bn_st'):
    res = bn_st()
    relic.bn_add(byref(res), pointer(a), pointer(b))
    relic.bn_mod_basic(byref(res), pointer(res), pointer(p))
    return res

def fp_mul(a:'bn_st', b:'bn_st'):
    res = bn_st()
    relic.bn_mul_karat(byref(res), pointer(a), pointer(b))
    relic.bn_mod_basic(byref(res), pointer(res), pointer(p))
    return res

# return \sum{k_i * h_i}
def ep_mul_sim_lot(k_set, h_set, n):
    res = ep_st()

    h_set_ctype = (ep_st * n)(*h_set)
    k_set_ctype = (bn_st * n)(*k_set)

    relic.ep_mul_sim_lot(byref(res), pointer(h_set_ctype), pointer(k_set_ctype), n)
    return res

def key_gen():
    sk = bn_rand_mod(p)
    pk = ep_mul_gen(sk)
    return sk, pk

def hash_point(point:'ep_st'):
    k_pytype = int(sha256(pt_to_bytes(point)).hexdigest(), 16) % p_pytype
    k = long_to_bn(k_pytype)
    new_point = ep_mul_gen(k)
    return new_point

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
        sk_inv = bn_mod_inv(SK_pi[j], p)
        I_array[j] = ep_mul(sk_inv, H_array[pi][j])   # compute tag for linkable property
    
    for i in range(n):
        if i != pi:
            c_array[i] = bn_rand_mod(p)
    for j in range(m):
        r_array[j] = bn_rand_mod(p)
        L_array[j] = ep_mul_gen(r_array[j])
        R_array[j] = ep_mul(r_array[j], I_array[j])

        c_array_sim, PK_sim, H_array_sim = [], [], []
        for i in range(n):
            if i != pi:
                c_array_sim.append(c_array[i])
                PK_sim.append(PK[i][j])
                H_array_sim.append(H_array[i][j])
                
        L_array[j] = ep_add(L_array[j], ep_mul_sim_lot(c_array_sim, PK_sim, n - 1))
        R_array[j] = ep_add(R_array[j], ep_mul_sim_lot(c_array_sim, H_array_sim, n - 1))
    
    c_pytype = int(sha256(M.encode() + ptlist_to_bytes(L_array) + ptlist_to_bytes(R_array)).hexdigest(), 16) % p_pytype
    c = long_to_bn(c_pytype)
    
    c_array[pi] = bn_zero()
    for i in range(n):
        if i != pi:
            c_array[pi] = fp_add(c_array[pi], c_array[i])
    c_array[pi] = fp_sub(c, c_array[pi])

    for j in range(m):
        s_array[j] = fp_sub(r_array[j], fp_mul(c_array[pi], SK_pi[j]))
    
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
        L_array[j] = ep_mul_gen(s_array[j])
        R_array[j] = ep_mul(s_array[j], I_array[j])

        PK_sim, H_array_sim = [], []
        for i in range(n):
            PK_sim.append(PK[i][j])
            H_array_sim.append(H_array[i][j])
        L_array[j] = ep_add(L_array[j], ep_mul_sim_lot(c_array, PK_sim, n))
        R_array[j] = ep_add(R_array[j], ep_mul_sim_lot(c_array, H_array_sim, n))
        
    c = bn_zero()
    for i in range(n):
        c = fp_add(c, c_array[i])

    c_pytype = c.dp[0] + (c.dp[1] << 64) + (c.dp[2] << 128) + (c.dp[3] << 192)
    c_vrf_pytype = int(sha256(M.encode() + ptlist_to_bytes(L_array) + ptlist_to_bytes(R_array)).hexdigest(), 16) % p_pytype

    if c_pytype != c_vrf_pytype:
        return 0
    return 1

# Loop in NISA Proof
# u: Hash(P, generator_u, c)
def P_proof(g_list, u, a, b, L, R):
    n = len(a)
    if n == 1:
        return L, R, a, b
    n_half = n // 2
    c_L, c_R = bn_zero(), bn_zero()
    for i in range(n_half):
        c_L = fp_add(c_L, fp_mul(a[i], b[n_half + i]))
        c_R = fp_add(c_R, fp_mul(a[n_half + i], b[i]))
    L_cur, R_cur = ep_mul(c_L, u), ep_mul(c_R, u)
    # for i in range(n_half):
    #     L_cur = ep_add(L_cur, ep_mul(a[i], g_list[n_half + i]))
    #     R_cur = ep_add(R_cur, ep_mul(a[n_half + i], g_list[i]))
    L_cur = ep_add(L_cur, ep_mul_sim_lot(a[:n_half], g_list[n_half:], n_half))
    R_cur = ep_add(R_cur, ep_mul_sim_lot(a[n_half:], g_list[:n_half], n_half))
    L.append(L_cur)
    R.append(R_cur)
    x_pytype = int(sha256(pt_to_bytes(L_cur) + pt_to_bytes(R_cur)).hexdigest(), 16) % p_pytype
    x = long_to_bn(x_pytype)
    x_inv = bn_mod_inv(x, p)
    g_list_new = [None] * n_half
    b_value = fp_add(fp_mul(x_inv, b[0]), fp_mul(x, b[n_half]))
    a_new, b_new = [None] * n_half, [b_value] * n_half
    for i in range(n_half):
        g_list_new[i] = ep_add(ep_mul(x_inv, g_list[i]), ep_mul(x, g_list[n_half + i]))
        a_new[i] = fp_add(fp_mul(x, a[i]), fp_mul(x_inv, a[n_half + i]))
    return P_proof(g_list_new, u, a_new, b_new, L, R)

def NISA_proof(g_list, P, c, a):
    concat_str = pt_to_bytes(P) + pt_to_bytes(generator_u)
    for i in range(3, -1, -1):
        concat_str += long_to_bytes(c.dp[i])
    u_coef_pytype = int(sha256(concat_str).hexdigest(), 16) % p_pytype
    u_coef = long_to_bn(u_coef_pytype)
    
    u = ep_mul(u_coef, generator_u)
    b_value = bn_st()
    relic.bn_set_dig(byref(b_value), 1)
    b = [b_value] * len(a)
    return P_proof(g_list, u, a, b, [], [])

# helper method to check if i's j-th bit is 1
def check_bit(i, j):
    return (i >> j) & 1

def NISA_vrf(g_list, P, c, NISA_pi):
    L, R, a, b = NISA_pi[0], NISA_pi[1], NISA_pi[2][0], NISA_pi[3][0]
    n, logn = len(g_list), len(L)
    x, x_inv = [None] * logn, [None] * logn
    y = [None] * n
    for i in range(n):
        y_i = bn_st()
        relic.bn_set_dig(byref(y_i), 1)
        y[i] = y_i

    concat_str = pt_to_bytes(P) + pt_to_bytes(generator_u)
    for i in range(3, -1, -1):
        concat_str += long_to_bytes(c.dp[i])
    u_coef_pytype = int(sha256(concat_str).hexdigest(), 16) % p_pytype
    u_coef = long_to_bn(u_coef_pytype)
    u = ep_mul(u_coef, generator_u)

    new_P = ep_add(P, ep_mul(c, u))
    for j in range(logn):
        x_j_pytype = int(sha256(pt_to_bytes(L[j]) + pt_to_bytes(R[j])).hexdigest(), 16) % p_pytype
        x[j] = long_to_bn(x_j_pytype)
        x_inv[j] = bn_mod_inv(x[j], p)
    for i in range(n):
        for j in range(len(L)):
            if check_bit(i, j) == 1:
                y[i] = fp_mul(y[i], x[logn - 1 - j])
            else:
                y[i] = fp_mul(y[i], x_inv[logn - 1 - j]) 
    check_left = new_P
    # for j in range(logn):
    #     check_left = ep_add(check_left, ep_mul(fp_mul(x[j], x[j]), L[j]))
    #     check_left = ep_add(check_left, ep_mul(fp_mul(x_inv[j], x_inv[j]), R[j]))
    for j in range(logn):
        x[j] = fp_mul(x[j], x[j])
        x_inv[j] = fp_mul(x_inv[j], x_inv[j])
    check_left = ep_add(check_left, ep_mul_sim_lot(x, L, logn))
    check_left = ep_add(check_left, ep_mul_sim_lot(x_inv, R, logn))

    check_right = ep_mul(fp_mul(a, b), u)
    # for i in range(n):
    #     check_right = ep_add(check_right, ep_mul(fp_mul(a, y[i]), g_list[i]))
    for i in range(n):
        y[i] = fp_mul(a, y[i])
    check_right = ep_add(check_right, ep_mul_sim_lot(y, g_list, n))

    if relic.ep_cmp(byref(check_left), byref(check_right)) == 0:
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
        sk_inv = bn_mod_inv(SK_pi[j], p)
        I_array[j] = ep_mul(sk_inv, H_array[pi][j])   # compute tag for linkable property
    
    for i in range(n):
        if i != pi:
            c_array[i] = bn_rand_mod(p)
    for j in range(m):
        r_array[j] = bn_rand_mod(p)
        L_array[j] = ep_mul_gen(r_array[j])
        R_array[j] = ep_mul(r_array[j], I_array[j])

        c_array_sim, PK_sim, H_array_sim = [], [], []
        for i in range(n):
            if i != pi:
                c_array_sim.append(c_array[i])
                PK_sim.append(PK[i][j])
                H_array_sim.append(H_array[i][j])
                
        L_array[j] = ep_add(L_array[j], ep_mul_sim_lot(c_array_sim, PK_sim, n - 1))
        R_array[j] = ep_add(R_array[j], ep_mul_sim_lot(c_array_sim, H_array_sim, n - 1))
    
    c_pytype = int(sha256(M.encode() + ptlist_to_bytes(L_array) + ptlist_to_bytes(R_array)).hexdigest(), 16) % p_pytype
    c = long_to_bn(c_pytype)
    
    c_array[pi] = bn_zero()
    for i in range(n):
        if i != pi:
            c_array[pi] = fp_add(c_array[pi], c_array[i])
    c_array[pi] = fp_sub(c, c_array[pi])

    for j in range(m):
        s_array[j] = fp_sub(r_array[j], fp_mul(c_array[pi], SK_pi[j]))

    # compress size to log(n)
    alpha, beta = [None] * m, [None] * m
    g_list = [None] * n

    for j in range(m):
        alpha_pytype = int(sha256(M.encode() + pt_to_bytes(L_array[j])).hexdigest(), 16) % p_pytype
        alpha[j] = long_to_bn(alpha_pytype)
        beta_pytype = int(sha256(M.encode() + pt_to_bytes(R_array[j])).hexdigest(), 16) % p_pytype
        beta[j] = long_to_bn(beta_pytype)

    for i in range(n):
        g_list[i] = ep_add(ep_mul_sim_lot(alpha, PK[i], m), ep_mul_sim_lot(beta, H_array[i], m))
    L_sim, R_sim = [], []
    for j in range(m):
        L_sim.append(ep_sub(L_array[j], ep_mul_gen(s_array[j])))
        R_sim.append(ep_sub(R_array[j], ep_mul(s_array[j], I_array[j])))
    P = ep_add(ep_mul_sim_lot(alpha, L_sim, m), ep_mul_sim_lot(beta, R_sim, m))
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

    for j in range(m):
        alpha_pytype = int(sha256(M.encode() + pt_to_bytes(L_array[j])).hexdigest(), 16) % p_pytype
        alpha[j] = long_to_bn(alpha_pytype)
        beta_pytype = int(sha256(M.encode() + pt_to_bytes(R_array[j])).hexdigest(), 16) % p_pytype
        beta[j] = long_to_bn(beta_pytype)

    for i in range(n):
        g_list[i] = ep_add(ep_mul_sim_lot(alpha, PK[i], m), ep_mul_sim_lot(beta, H_array[i], m))
    L_sim, R_sim = [], []
    for j in range(m):
        L_sim.append(ep_sub(L_array[j], ep_mul_gen(s_array[j])))
        R_sim.append(ep_sub(R_array[j], ep_mul(s_array[j], I_array[j])))
    P = ep_add(ep_mul_sim_lot(alpha, L_sim, m), ep_mul_sim_lot(beta, R_sim, m))

    c_pytype = int(sha256(M.encode() + ptlist_to_bytes(L_array) + ptlist_to_bytes(R_array)).hexdigest(), 16) % p_pytype
    c = long_to_bn(c_pytype)

    return NISA_vrf(g_list, P, c, NISA_pi)
    
if __name__ == '__main__':
    # relic.bn_print(byref(p))
    # print(hex(p_pytype)[2:])

    PK_num, m = 20, 10
    SK_pi = [None] * m
    for pi in tqdm(range(PK_num)):
        PK_set = [[None] * m] * PK_num
        for i in range(PK_num):
            for j in range(m):
                _, PK_set[i][j] = key_gen()
        for j in range(m):
            SK_pi[j], PK_set[pi][j] = key_gen()
        sigma = wlc_basic_sign("F0r_wlc_basic_t3st1nG", PK_set, SK_pi, pi)
        if wlc_basic_vrf("F0r_wlc_basic_t3st1nG", PK_set, sigma) != 1:
            print("failed")
    print("[*] wlc (without NISA) passed")

    PK_num, m = 20, 50
    time_trail = 10
    PK_set = [[None] * m] * PK_num
    SK_set = [[None] * m] * PK_num
    for i in range(PK_num):
        for j in range(m):
            SK_set[i][j], PK_set[i][j] = key_gen()
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
    print('Average sign_cost (without NISA, n=20, m=50):', sign_cost / time_trail, 's')
    print('Average vrf_cost (without NISA, n=20, m=50):', vrf_cost / time_trail, 's')

    PK_num = 2**5
    g_list = [None] * PK_num
    c_array = [None] * PK_num
    c = bn_zero()
    for i in range(PK_num):
        _, g_list[i] = key_gen()
        c_array[i] = bn_rand_mod(p)
        c = fp_add(c, c_array[i])
    P = ep_mul_sim_lot(c_array, g_list, PK_num)
    NISA_pi = NISA_proof(g_list, P, c, c_array)
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
                _, PK_set[i][j] = key_gen()
        for j in range(m):
            SK_pi[j], PK_set[pi][j] = key_gen()
        sigma = wlc_formal_sign("F0r_wlc_formal_t3st1nG", PK_set, SK_pi, pi)
        if wlc_formal_vrf("F0r_wlc_formal_t3st1nG", PK_set, sigma) != 1:
            print("failed")
    print("[*] wlc (with NISA) passed")

    PK_num, m = 2**5, 20
    time_trail = 10
    PK_set = [[None] * m] * PK_num
    SK_set = [[None] * m] * PK_num
    for i in range(PK_num):
        for j in range(m):
            SK_set[i][j], PK_set[i][j] = key_gen()
    sign_cost, vrf_cost = 0, 0
    for k in range(time_trail):
        rand_pi = secrets.randbelow(PK_num)
        start_time = time.time()
        sigma = wlc_formal_sign("F0r_wlc_formal_t3st1nG", PK_set, SK_pi, pi)
        end_time = time.time()
        sign_cost += (end_time - start_time)
        start_time = time.time()
        wlc_formal_vrf("F0r_wlc_formal_t3st1nG", PK_set, sigma)
        end_time = time.time()
        vrf_cost += (end_time - start_time)
    print('Average sign_cost (with NISA, n=32, m=20):', sign_cost / time_trail, 's')
    print('Average vrf_cost (with NISA, n=32, m=20):', vrf_cost / time_trail, 's')