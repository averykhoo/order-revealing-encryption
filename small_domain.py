"""
based on Section 3: `ORE for Small Domains`
"""
import enum
import random

N = 4096  # space of all possible messages
lmbda = 64  # security parameter


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
    Let F : {0, 1} ** λ × {0, 1} ** λ → {0, 1} ** λ be a secure PRF

    The correct implementation for this would probably be a HMAC of some kind

    :param secret_key:
    :param data:
    :return:
    """
    return hash(('salt', secret_key, data)) & ((1 << lmbda) - 1)


def H(data1, data2):
    """
    H : {0, 1} ** λ × {0, 1} ** λ → Z₃ be a hash function (modeled as a random oracle in the security proof)

    The correct implementation of this would probably be a cryptographic hash like SHA

    :param data:
    :return:
    """
    return hash(('salt', data1, data2)) % len(CompareResult)


def permute(permutation, data):
    return permutation[data]


def ore_setup():
    """
    On input a security parameter λ, the setup algorithm outputs a secret key sk.
    The setup algorithm samples a PRF key k ← {0, 1} ** λ for F,
        and a uniformly random permutation π : [N] → [N].
    The secret key sk is the pair (k, π).

    :return:
    """
    k = random.randint(0, (1 << lmbda) - 1)
    pi = list(range(N))
    random.shuffle(pi)
    return k, pi


def ore_encrypt_left(secret_key, message):
    """
    On input a secret key sk and a message m ∈ D, the encryption algorithm outputs a ciphertext ct.
    Write sk as (k, π).
    The left encryption algorithm computes and returns the tuple ct(L) = (F(k, π(x)), π(x)).

    :param secret_key:
    :param message:
    :return:
    """
    k, pi = secret_key
    permuted_message = permute(pi, message)
    return F(k, permuted_message), permuted_message


def ore_encrypt_right(secret_key, message):
    """
    On input a secret key sk and a message m ∈ D, the encryption algorithm outputs a ciphertext ct.
    Write sk as (k, π).
    First, the right encryption algorithm samples a random nonce r ← {0, 1} ** λ.
    Then, for each i ∈ [N], it computes the value v(i) = cmp(π⁻¹(i), y) + H(F(k, i), r) (mod 3).
    Finally, it outputs the ciphertext ct(R) = (r, v(1), v(2), ... , v(N)).

    :param secret_key:
    :param message:
    :return:
    """

    # invert pi
    k, pi = secret_key
    pi_inverse = [-1] * len(pi)
    for i, x in enumerate(pi):
        pi_inverse[x] = i

    # random nonce
    nonce = random.randint(0, (1 << lmbda) - 1)

    # compute each v(i)
    # note: instead of computing for each ciphertext, we could instead compute for each plaintext
    # but since this is how the paper is written, we'll do it this way
    out = [nonce]
    for ciphertext in range(N):
        plaintext = permute(pi_inverse, ciphertext)
        v_i = (cmp(plaintext, message) + H(F(k, ciphertext), nonce)) % len(CompareResult)
        out.append(v_i)
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
    k_prime, h = ciphertext_left
    nonce = ciphertext_right[0]
    v_i = ciphertext_right[h + 1]
    return (v_i - H(k_prime, nonce)) % len(CompareResult)


if __name__ == '__main__':
    sk = ore_setup()
    print(f'{sk=}')
    for j in range(N):
        print(j)
        ct_r = ore_encrypt_right(sk, j)
        for i in range(N):
            ct_l = ore_encrypt_left(sk, i)
            cmp_result = ore_compare(ct_l, ct_r)
            assert cmp(i, j) == cmp_result
            # print(i, j, ct_l, ct_r)
