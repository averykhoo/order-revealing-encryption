"""
based on Section 4: `Domain Extension: A Large-Domain ORE`
"""
import enum
import random
from typing import Tuple

N = 4096  # space of all possible messages
lmbda = 64  # security parameter such that poly(lmbda) = N

# d, n > 0 such that d ** n ≥ N
d = 1 << 4  # for my implementation below, d must be a non-zero power of 2, and should be less than 2**lmbda
n = 5


class CompareResult(enum.IntEnum):
    EQUALS = 0
    GREATER_THAN = 1
    LESS_THAN = 2  # == -1 % 3


def cmp(left, right):
    """


    :param left:
    :param right:
    :return:
    """
    if left == right:
        return CompareResult.EQUALS.value
    if left > right:
        return CompareResult.GREATER_THAN.value
    if left < right:
        return CompareResult.LESS_THAN.value


def F(secret_key, data):
    """
    Let F : {0, 1} ** λ × [N] → {0, 1} ** λ be a secure PRF on variable-length inputs

    The correct implementation for this would probably be HMAC-SHA3 or something like that
    Note that data can have length zero

    :param secret_key:
    :param data:
    :return:
    """
    return hash(('salt', secret_key, data)) & ((1 << lmbda) - 1)


def H(data1, data2):
    """
    H : {0, 1} ** λ × {0, 1} ** λ → Z₃ be a hash function (modeled as a random oracle)

    The correct implementation of this would probably be a cryptographic hash like SHA

    :param data:
    :return:
    """
    return hash(('salt', data1, data2)) % len(CompareResult)


def permute(secret_key, data):
    """
    Let π : {0, 1} ** λ × [d] → [d] be a secure PRP

    Based off the paper this needs to be invertible, so it might need to be an encryption function
    In this case, it's xor based, so it is its own inverse

    :param secret_key:
    :param data:
    :return:
    """
    return (data ^ secret_key) & (d - 1)


def ore_setup():
    """
    On input a security parameter λ, the setup algorithm outputs a secret key sk.
    The setup algorithm samples PRF keys k1, k2 ← {0, 1} ** λ for F.
    The master secret key sk is the pair (k1, k2).

    :return:
    """
    k1 = random.randint(0, (1 << lmbda) - 1)
    k2 = random.randint(0, (1 << lmbda) - 1)
    return k1, k2


def ore_encrypt_left(secret_key, message: Tuple[int, ...]):
    """
    Let sk = (k1, k2).
    For each i ∈ [n], the left encryption algorithm first computes x˜ = π(F(k2, x|i−1), xi)
        and then sets u(i) = (F(k1, x|i−1kx˜), x˜).
    It returns the ciphertext ct(L) = (u(1), ... , u(n)).

    Notes:
        small n is the length of the message
        i is the index of a character in the message, starting at 1
        the message is assumed to be d-ary (i.e. the alphabet is of size d)
        x|i-1 is all elements of x from 1 to i-1, and may be an empty list


    :param secret_key:
    :param message:
    :return:
    """
    k1, k2 = secret_key

    out = []
    for i, x_i in enumerate(message):
        permuted_message = permute(F(k2, message[:i]), x_i)
        out.append((F(k1, message[:i] + (permuted_message,)), permuted_message))

    return out


def ore_encrypt_right(secret_key, message):
    """
    Let sk = (k1, k2).
    First, the right encryption algorithm uniformly samples a nonce r ← {0, 1} ** λ.
    Then, for each i ∈ [n] and j ∈ [d], letting j∗ = π⁻¹(F(k2, y|i−1), j),
        it computes z(i,j) = cmp(j∗, y(i)) + H(F(k1, y|i−1kj), r) (mod 3).
    It then defines the tuple vi = (z(i,1), ... , z(i,d))
        and outputs the ciphertext ct(R) = (r, v(1), v(2), ... , v(n)).

    :param secret_key:
    :param message:
    :return:
    """

    # invert pi
    k1, k2 = secret_key

    # random nonce
    nonce = random.randint(0, (1 << lmbda) - 1)

    out = [nonce]
    for i, y_i in enumerate(message):
        v_i = []
        for cipher_char in range(d):
            plain_char = permute(F(k2, message[:i]), cipher_char)
            v_i.append(cmp(plain_char, y_i) + H(F(k1, message[:i] + (cipher_char,)), nonce))
        out.append(tuple(v_i))

    return tuple(out)


def ore_compare(ciphertext_left, ciphertext_right):
    """
    On input two ciphertexts ct1, ct2, the compare algorithm outputs a bit b ∈ {0, 1}.
    The compare algorithm first parses ct(L) = (k', h) and ct(R) = (r, v(1), v(2), ... , v(N)),
        and then outputs the result v(h) − H(k', r) (mod 3).

    :param ciphertext_left:
    :param ciphertext_right:
    :return:
    """
    nonce = ciphertext_right[0]
    for u_i, v_i in zip(ciphertext_left, ciphertext_right[1:]):
        k_i_prime, h_i = u_i
        z_i = v_i[h_i]
        cmp_result = z_i - H(k_i_prime, nonce) % len(CompareResult)
        if cmp_result != 0:
            return cmp_result

    return 0


if __name__ == '__main__':
    messages = []
    for _ in range(1000):
        messages.append(tuple(random.randint(0, d - 1) for _ in range(n)))

    sk = ore_setup()
    print(f'{sk=}')
    for j in messages:
        print(j)
        ct_r = ore_encrypt_right(sk, j)
        for i in messages:
            ct_l = ore_encrypt_left(sk, i)
            cmp_result = ore_compare(ct_l, ct_r)
            assert cmp(i, j) == cmp_result
            # print(i, j, ct_l, ct_r)
