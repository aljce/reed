import cmath

i = complex(0, 1)
tau = 2 * cmath.pi

def fftSlow(x):
    n = len(x)
    res = []
    for k in range(0, n):
        s = 0
        for l in range(0, n):
            s += x[l] * cmath.exp(i * tau * k * l / n)
        res.append(s)
    return res

def split(xs):
    es , os = [] , []
    parity = False
    for x in xs:
        if parity:
            os.append(x)
        else:
            es.append(x)
        parity = not parity
    return es , os

def isPowerOfTwo(n):
    if (n == 0):
        return False
    else:
        while (1 < n):
            if (n % 2 != 0):
                return False
            n = n >> 1
        return True

# def cooley(x):
#     n = len(x)
#     if n <= 1: return [x[0]]
#     es , os = split(x)
#     fes , fos = cooley(es) , cooley(os)
#     res = n * [0]
#     for k in range(0, n // 2):
#         omega = cmath.exp(i * tau * k / n)
#         res[k] = fes[k] + omega * fos[k]
#         res[k + n // 2] = fes[k] - omega * fos[k]
#     return res

def cooley(x, r, n, start, stride):
    if n <= 1:
        return [x[start]]
    evens = cooley(x, r, n // 2, start + 0,      stride * 2)
    odds  = cooley(x, r, n // 2, start + stride, stride * 2)
    res = n * [0]
    for k in range(0, n // 2):
        omega = cmath.exp(i * tau * k / n)
        res[k] = evens[k] + omega * odds[k]
        res[k + n // 2] = evens[k] - omega * odds[k]
    return res

def fft(x):
    n = len(x)
    assert isPowerOfTwo(n), "length of input must be a power of two"
    return cooley(x, n * [0], n, 0, 1)

def pretty(x):
    def truncate(f, n):
        strFormNum = "{0:." + str(n+5) + "f}"
        trunc_num = float(strFormNum.format(f)[:-5])
        return trunc_num
    def show(c):
        n = 5
        return str(truncate(c.real, n)) + " + " + str(truncate(c.imag, n)) + "i"
    return str([ show(c) for c in x ])

def test(x):
    print(pretty(x))
    print(pretty(fftSlow(x)))
    print(pretty(fft(x)))

seq = [0, 0.707106, 1, 0.707106, 0, -0.707106, -1, -0.707106]
test(seq)

# def old(x):
#     n = len(x)
#     if n <= 1:
#         print(x[0])
#         return
#     es , os = split(x)
#     old(es)
#     old(os)

# def fast(x, n, start, stride):
#     if n <= 1:
#         print(x[start])
#         return
#     m = n // 2
#     fast(x, m, start + 0, stride * 2)
#     fast(x, m, start + stride, stride * 2)

# def new(x):
#     fast(x, len(x), 0, 1)

# seq = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
# print(old(seq))
# print("")
# print(new(seq))

# def Complex(F):
#     class Complex(Field):
#         def __init__(self, real, imag):
#             self.real = real
#             self.imag = imag
#         def __str__(self):
#             return str(self.real) + " + " + str(self.imag) + "i"
#         def zero():
#             return Complex(F.zero(), F.zero())
#         def one():
#             return Complex(F.one(),  F.zero())
#         def add(x, y):
#             return Complex(x.real + y.real, x.imag + y.imag)
#         def neg(x):
#             return Complex(neg(x.real), neg(x.imag))
#         def mult(x, y):
#             return Complex()
#         def inverse(x):
#             den = x.real * x.real + x.imag * x.imag
#             return Complex(x.real / den, neg(x.imag) / den)
#         def i():
#             return Complex(F.zero(), F.one())
#     return Complex

# CC = Complex(Real())
# print(CC.neg(CC.one()))

# tau = 2 * cmath.pi

# def wave(n, f):
#     res = []
#     j = 0
#     while (j < n):
#         res.append(math.sin(tau * f * j))
#         j += 1
#     return res


# def cooley(x, n, off):
#     if n <= 1: return
#     m = n // 2
#     theta = tau / n
#     for s in range(0, m):
#         omega = complex(cmath.cos(s * theta), -cmath.sin(s * theta))
#         a = x[s + off + 0]
#         b = x[s + off + m]
#         x[s + off + 0] = a + b
#         x[s + off + m] = (a - b) * omega
#     cooley(x, m, off + 0)
#     cooley(x, m, off + m)


# def fft(x):
#     n = len(x)
#     assert isPowerOfTwo(n), "length of input must be a power of two"
#     cooley(x, n, 0)

# def test(x):
#     print(x)
#     fft(x)
#     print(x)

# # seq = wave(8, 1)
# # seq = [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
# seq = [complex(1, 0), complex(2, -1), complex(0, -1), complex(-1, 2)]
# test(seq)
