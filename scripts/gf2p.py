
# a set of useful functions for manipulating gf(2) polynomials
#

# convert le bytes into a bigint
def from_le_bytes(x):
    r = 0
    for i, x in enumerate(xs):
        r |= x << 8*i
    return r

# convert bigint to array of le bytes
def to_le_bytes(x):
    r = []
    while x:
        r.append(0xff & x)
        x >>= 8
    return r

# carry-less multiplication
def xmul(a, b):
    x = 0
    while a:
        if a & 1:
            x ^= b
        a >>= 1
        b <<= 1
    return x

# carry-less division
def xdiv(a, b):
    # maybe not the best but gets the job done
    x = 0
    while a.bit_length() >= b.bit_length():
        x ^= 1 << a.bit_length()-b.bit_length()
        a ^= b << a.bit_length()-b.bit_length()
    return x
    
# carry-less remainder
def xmod(a, b):
    # maybe not the best but gets the job done
    while a.bit_length() >= b.bit_length():
        a ^= b << a.bit_length()-b.bit_length()
    return a

# naive mul based on naive xmod
def gfmul_naive(a, b, p=0x11b):
    return xmod(xmul(a, b), p)

# naive div, a/b = a*b^-1 = a*b^254
def gfdiv_naive(a, b, p=0x11b):
    b2   = gfmul_naive(b,    b,    p)
    b3   = gfmul_naive(b2,   b,    p)
    b6   = gfmul_naive(b3,   b3,   p)
    b12  = gfmul_naive(b6,   b6,   p)
    b15  = gfmul_naive(b12,  b3,   p)
    b24  = gfmul_naive(b12,  b12,  p)
    b48  = gfmul_naive(b24,  b24,  p)
    b63  = gfmul_naive(b48,  b15,  p)
    b126 = gfmul_naive(b63,  b63,  p)
    b127 = gfmul_naive(b126, b,    p)
    b254 = gfmul_naive(b127, b127, p)

    return gfmul_naive(a, b254, p)

# generate gf log/inverse-log tables
def gfgen_tables(p=0x11b, g=0x3, elements=256):
    gflog = [0]*elements
    gfexp = [0]*elements

    x = 1
    for i in range(elements):
        gflog[x] = i % elements
        gfexp[i] = x % elements
        x = xmul(x, g)
        if x >= elements:
            x ^= p
        assert x < elements

    gflog[0] = 0xff # log(0) is undefined
    gflog[1] = 0x00 # log(1) is 0
    return gflog, gfexp

gflog, gfexp = gfgen_tables()

# table based mul
def gfmul_tables(a, b, gflog=gflog, gfexp=gfexp):
    if a == 0 or b == 0:
        return 0
    else:
        x = gflog[a] + gflog[b]
        return gfexp[x-255 if x >= 255 else x]

# table based div
def gfdiv_tables(a, b, gflog=gflog, gfexp=gfexp):
    return gfmul_table(
        a,
        gfexp[0xff - gflog[b]],
        gflog=gflog, gfexp=gfexp)

# generate Barret reduction constant
def gfgen_barret(p=0x11b):
    return xdiv(0x10000, p)

# gf mul using Barret reduction
def gfmul_barret(a, b, p=0x11b, p_i=gfgen_barret(0x11b)):
    x = xmul(a, b)
    q = xmul(x >> 8, p_i) >> 8
    return 0xff & (xmul(q, p) ^ x)

# naive div, a/b = a*b^-1 = a*b^254
def gfdiv_barret(a, b, p=0x11b, p_i=gfgen_barret(0x11b)):
    b2   = gfmul_barret(b,    b,    p, p_i)
    b3   = gfmul_barret(b2,   b,    p, p_i)
    b6   = gfmul_barret(b3,   b3,   p, p_i)
    b12  = gfmul_barret(b6,   b6,   p, p_i)
    b15  = gfmul_barret(b12,  b3,   p, p_i)
    b24  = gfmul_barret(b12,  b12,  p, p_i)
    b48  = gfmul_barret(b24,  b24,  p, p_i)
    b63  = gfmul_barret(b48,  b15,  p, p_i)
    b126 = gfmul_barret(b63,  b63,  p, p_i)
    b127 = gfmul_barret(b126, b,    p, p_i)
    b254 = gfmul_barret(b127, b127, p, p_i)

    return gfmul_barret(a, b254, p, p_i)

# test all multiply implementations
def gftest_mul(p=0x11b, g=0x3, number=10):
    gflog, gfexp = gfgen_tables(p, g)
    p_i = gfgen_barret(p)

    expected = [0]*256*256
    for x in range(256):
        for y in range(256):
            expected[x+y*256] = gfmul_naive(x, y, p)

    def test_gfmul_naive():
        for x in range(256):
            for y in range(256):
                res = gfmul_naive(x, y, p)
                assert res == expected[x+y*256], (
                    "gfmul_naive failed => "
                    "0x%02x * 0x%02x = 0x%02x, expected 0x%02x" %
                    (x, y, res, expected[x+y*256]))

    def test_gfmul_tables():
        for x in range(256):
            for y in range(256):
                res = gfmul_tables(x, y, gflog, gfexp)
                assert res == expected[x+y*256], (
                    "gfmul_tables failed => "
                    "0x%02x * 0x%02x = 0x%02x, expected 0x%02x" %
                    (x, y, res, expected[x+y*256]))

    def test_gfmul_barret():
        for x in range(256):
            for y in range(256):
                res = gfmul_barret(x, y, p, p_i)
                assert res == expected[x+y*256], (
                    "gfmul_barret failed => "
                    "0x%02x * 0x%02x = 0x%02x, expected 0x%02x" %
                    (x, y, res, expected[x+y*256]))

    import timeit
    print("running...")
    print("gfmul_naive  => %.3fs" % (timeit.timeit(test_gfmul_naive,  number=number)/number))
    print("gfmul_tables => %.3fs" % (timeit.timeit(test_gfmul_tables, number=number)/number))
    print("gfmul_barret => %.3fs" % (timeit.timeit(test_gfmul_barret, number=number)/number))

# test all division implementations
def gftest_div(p=0x11b, g=0x3, number=10):
    gflog, gfexp = gfgen_tables(p, g)
    p_i = gfgen_barret(p)

    expected = [0]*256*256
    for x in range(256):
        for y in range(1, 256):
            expected[x+y*256] = gfdiv_naive(x, y, p)

    def test_gfdiv_naive():
        for x in range(256):
            for y in range(1, 256):
                res = gfdiv_naive(x, y, p)
                assert res == expected[x+y*256], (
                    "gfdiv_naive failed => "
                    "0x%02x * 0x%02x = 0x%02x, expected 0x%02x" %
                    (x, y, res, expected[x+y*256]))

    def test_gfdiv_tables():
        for x in range(256):
            for y in range(1, 256):
                res = gfdiv_tables(x, y, gflog, gfexp)
                assert res == expected[x+y*256], (
                    "gfdiv_tables failed => "
                    "0x%02x * 0x%02x = 0x%02x, expected 0x%02x" %
                    (x, y, res, expected[x+y*256]))

    def test_gfdiv_barret():
        for x in range(256):
            for y in range(1, 256):
                res = gfdiv_barret(x, y, p, p_i)
                assert res == expected[x+y*256], (
                    "gfdiv_barret failed => "
                    "0x%02x * 0x%02x = 0x%02x, expected 0x%02x" %
                    (x, y, res, expected[x+y*256]))

    import timeit
    print("running...")
    print("gfdiv_naive  => %.3fs" % (timeit.timeit(test_gfdiv_naive,  number=number)/number))
    print("gfdiv_tables => %.3fs" % (timeit.timeit(test_gfdiv_tables, number=number)/number))
    print("gfdiv_barret => %.3fs" % (timeit.timeit(test_gfdiv_barret, number=number)/number))

