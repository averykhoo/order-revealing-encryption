"""
based on Section 5: `Encrypted Range Queries`
"""
import bisect
import enum
import math
import random
from dataclasses import dataclass
from dataclasses import field
from typing import Dict
from typing import List
from typing import Sequence
from typing import Tuple

d = 1 << 4
n = 5
lmbda = 64  # security parameter such that d ** n == poly(lambda)

# for my implementation below, d must be a non-zero power of 2
assert d > 0
assert (d & (d - 1)) == 0

# to ensure randomness, d! (factorial) must be less than 2 ** lambda
assert sum(math.log2(i) for i in range(1, d + 1)) <= lmbda


class CompareResult(enum.IntEnum):
    EQUALS = 0
    GREATER_THAN = 1
    LESS_THAN = 2
    NAN = 3


def cmp_seq(left: Sequence[int], right: Sequence[int]):
    """
    compares 2 d-ary sequences of length n
    n must be the same

    :param left:
    :param right:
    :return:
    """
    assert len(left) == len(right) == n
    for _left, _right in zip(left, right):
        if (res := cmp_char(_left, _right)).value:
            return res
    return CompareResult.EQUALS


def cmp_char(left, right) -> CompareResult:
    """
    compares two d-ary chars

    :param left:
    :param right:
    :return:
    """
    assert 0 <= left < d
    assert 0 <= right < d
    if left == 0 or right == 0:  # let's pretend zero is like NaN and cannot be compared
        return CompareResult.NAN
    if left == right:
        return CompareResult.EQUALS
    if left > right:
        return CompareResult.GREATER_THAN
    if left < right:
        return CompareResult.LESS_THAN
    raise RuntimeError


def F(secret_key, data):
    """
    Let F : {0, 1} ** λ × [N] → {0, 1} ** λ be a secure PRF on variable-length inputs

    The correct implementation for this would probably be HMAC
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

    :param data1:
    :param data2:
    :return:
    """
    return hash(('salt', data1, data2)) % len(CompareResult)


def permute(secret_key: int, data: int) -> int:
    """
    Let π : {0, 1} ** λ × [d] → [d] be a secure PRP

    Based off the paper this needs to be invertible, so it might need to be an encryption function
    In this case, it's xor based, so it is its own inverse

    Since this is supposed to reveal nothing about the data, the secret key must have the domain d! (as in factorial)
        in this case, (16!) < (2 ** 64), so we do have enough randomness in the secret key
        but the way it's implemented here is obviously not random enough
        it would be better to rewrite the encrypt_right function so this can also be one-way

    :param secret_key:
    :param data:
    :return:
    """
    assert 0 <= secret_key < 1 << lmbda
    assert 0 <= data < d
    return (data ^ secret_key) & (d - 1)


def ore_setup() -> Tuple[int, int]:
    """
    On input a security parameter λ, the setup algorithm outputs a secret key sk.
    The setup algorithm samples PRF keys k1, k2 ← {0, 1} ** λ for F.
    The master secret key sk is the pair (k1, k2).

    Note:
        it would be interesting for k2 to be a random permutation of elements in the space [d]
        and for each iteration of F(k2, message) to re-permute k2 in some way related to the chars in message
        perhaps by mapping each char to an affine map of some kind, then applying them in some sequence
        like how the enigma cipher worked

    :return:
    """
    k1 = random.randint(0, (1 << lmbda) - 1)
    k2 = random.randint(0, (1 << lmbda) - 1)
    return k1, k2


def ore_encrypt_left(secret_key: Tuple[int, int],
                     message: Tuple[int, ...],
                     ) -> Tuple[Tuple[int, int], ...]:
    """
    Let sk = (k1, k2).
    For each i ∈ [n], the left encryption algorithm first computes x˜ = π(F(k2, x|i−1), xi)
        and then sets u(i) = (F(k1, x|i−1 || x˜), x˜).
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

    return tuple(out)


def ore_encrypt_right(secret_key: Tuple[int, int],
                      message: Tuple[int, ...],
                      ) -> Tuple[int, Tuple[Tuple[int, ...], ...]]:
    """
    Let sk = (k1, k2).
    First, the right encryption algorithm uniformly samples a nonce r ← {0, 1} ** λ.
    Then, for each i ∈ [n] and j ∈ [d], letting j∗ = π⁻¹(F(k2, y|i−1), j),
        it computes z(i,j) = cmp(j∗, y(i)) + H(F(k1, y|i−1 || j), r) (mod 3).
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

    out = []
    for i, y_i in enumerate(message):
        v_i = []
        for cipher_char in range(d):
            # as before, we could iterate over plaintext chars and create the enciphered chars instead
            # which would allow `permute` to be a one-way function (as long as it's still 1-to-1 for the domain of [d])
            plain_char = permute(F(k2, message[:i]), cipher_char)
            v_i.append(cmp_char(plain_char, y_i).value + H(F(k1, message[:i] + (cipher_char,)), nonce))
        out.append(tuple(v_i))

    return nonce, tuple(out)


def ore_compare(ciphertext_left: Tuple[Tuple[int, int], ...],
                ciphertext_right: Tuple[int, Tuple[Tuple[int, ...], ...]],
                ) -> CompareResult:
    """
    On input two ciphertexts ct1, ct2, the compare algorithm outputs a bit b ∈ {0, 1}.
    The compare algorithm first parses ct(L) = (k', h) and ct(R) = (r, v(1), v(2), ... , v(N)),
        and then outputs the result v(h) − H(k', r) (mod 3).

    :param ciphertext_left:
    :param ciphertext_right:
    :return:
    """
    nonce = ciphertext_right[0]
    for u_i, v_i in zip(ciphertext_left, ciphertext_right[1]):
        k_i_prime, h_i = u_i
        z_i = v_i[h_i]
        result_i = (z_i - H(k_i_prime, nonce)) % len(CompareResult)
        if result_i != 0:
            return CompareResult(result_i)

    return CompareResult.EQUALS


@dataclass(eq=False, frozen=True)
class DatabaseServer:
    _rows: List[Tuple[int, Tuple[Tuple[int, ...], ...]]] = field(default_factory=list)

    def bisect_left(self,
                    query: Tuple[Tuple[int, int], ...],
                    lo=0,
                    hi=None,
                    ) -> int:
        if lo < 0:
            raise ValueError('lo must be non-negative')
        if hi is None:
            hi = len(self._rows)
        while lo < hi:
            mid = (lo + hi) // 2
            if ore_compare(query, self._rows[mid]) is CompareResult.LESS_THAN:
                lo = mid + 1
            else:
                hi = mid
        return lo

    def bisect_right(self,
                     query: Tuple[Tuple[int, int], ...],
                     lo=0,
                     hi=None,
                     ) -> int:

        if lo < 0:
            raise ValueError('lo must be non-negative')
        if hi is None:
            hi = len(self._rows)
        while lo < hi:
            mid = (lo + hi) // 2
            if ore_compare(query, self._rows[mid]) is CompareResult.GREATER_THAN:
                hi = mid
            else:
                lo = mid + 1
        return lo

    def range(self,
              query_lo: Tuple[Tuple[int, int], ...],
              query_hi: Tuple[Tuple[int, int], ...],
              ) -> List[Tuple[int, Tuple[int, Tuple[Tuple[int, ...], ...]]]]:
        lo = self.bisect_left(query_lo)
        hi = self.bisect_right(query_hi)
        return [(idx, self._rows[idx]) for idx in range(lo, hi)]

    def add(self,
            ciphertext_left: Tuple[Tuple[int, int], ...],
            ciphertext_right: Tuple[int, Tuple[Tuple[int, ...], ...]],
            ) -> Tuple[int, Tuple[int, Tuple[Tuple[int, ...], ...]]]:
        assert ore_compare(ciphertext_left, ciphertext_right) is CompareResult.EQUALS
        idx = self.bisect_left(ciphertext_left)
        self._rows.insert(idx, ciphertext_right)
        return idx, ciphertext_right

    def remove(self,
               query: Tuple[Tuple[int, int], ...],
               ) -> Tuple[int, Tuple[int, Tuple[Tuple[int, ...], ...]]]:
        idx = self.bisect_left(query)
        if ore_compare(query, self._rows[idx]) is CompareResult.EQUALS:
            return idx, self._rows.pop(idx)
        else:
            raise KeyError


@dataclass
class DatabaseClient:
    database: DatabaseServer = field(default_factory=DatabaseServer)
    secret_key: Tuple[int, int] = field(default_factory=ore_setup)

    __decrypt: Dict[Tuple[int, Tuple[Tuple[int, ...], ...]], Tuple[int, ...]] = field(default_factory=dict)

    def _decrypt(self, ciphertext_right: Tuple[int, Tuple[Tuple[int, ...], ...]]) -> Tuple[int, ...]:
        return self.__decrypt[ciphertext_right]

    def bisect_left(self,
                    query: Tuple[int, ...],
                    lo=0,
                    hi=None,
                    ) -> int:
        return self.database.bisect_left(ore_encrypt_left(self.secret_key, query), lo, hi)

    def bisect_right(self,
                     query: Tuple[int, ...],
                     lo=0,
                     hi=None,
                     ) -> int:
        return self.database.bisect_right(ore_encrypt_left(self.secret_key, query), lo, hi)

    def range(self,
              query_lo: Tuple[int, ...],
              query_hi: Tuple[int, ...],
              ) -> List[Tuple[int, Tuple[int, ...]]]:
        _query_lo = ore_encrypt_left(self.secret_key, query_lo)
        _query_hi = ore_encrypt_left(self.secret_key, query_hi)
        return [(idx, self._decrypt(ct_right)) for idx, ct_right in self.database.range(_query_lo, _query_hi)]

    def add(self,
            query: Tuple[int, ...],
            ) -> Tuple[int, Tuple[int, ...]]:
        ciphertext_right = ore_encrypt_right(self.secret_key, query)
        idx, ct_right = self.database.add(ore_encrypt_left(self.secret_key, query), ciphertext_right)
        assert ct_right == ciphertext_right
        self.__decrypt[ciphertext_right] = query
        return idx, self._decrypt(ct_right)

    def remove(self,
               query: Tuple[int, ...],
               ) -> Tuple[int, Tuple[int, ...]]:
        idx, ct_right = self.database.remove(ore_encrypt_left(self.secret_key, query))
        plaintext = self._decrypt(ct_right)
        del self.__decrypt[ct_right]
        return idx, plaintext


@dataclass(eq=False, frozen=True)
class MockDatabaseClient:
    _rows: List[Tuple[int]] = field(default_factory=list)

    def bisect_left(self,
                    query: Tuple[int, ...],
                    lo=0,
                    hi=None,
                    ) -> int:
        return bisect.bisect_left(self._rows, query, lo, hi)

    def bisect_right(self,
                     query: Tuple[int, ...],
                     lo=0,
                     hi=None,
                     ) -> int:

        return bisect.bisect_right(self._rows, query, lo, hi)

    def range(self,
              query_lo: Tuple[int, ...],
              query_hi: Tuple[int, ...],
              ) -> List[Tuple[int, Tuple[int, ...]]]:
        lo = self.bisect_left(query_lo)
        hi = self.bisect_right(query_hi)
        return [(idx, self._rows[idx]) for idx in range(lo, hi)]

    def add(self,
            query: Tuple[int, ...],
            ) -> Tuple[int, Tuple[int, ...]]:
        idx = self.bisect_left(query)
        self._rows.insert(idx, query)
        return idx, query

    def remove(self,
               query: Tuple[int, ...],
               ) -> Tuple[int, Tuple[int, ...]]:
        idx = self.bisect_left(query)
        if query == self._rows[idx]:
            return idx, self._rows.pop(idx)
        else:
            raise KeyError


if __name__ == '__main__':
    messages = []
    for _ in range(2000):
        messages.append(tuple(random.randint(0, d - 1) for _ in range(n)))

    sk = ore_setup()
    print(f'{sk=}')
    for msg_right in messages:
        ct_r = ore_encrypt_right(sk, msg_right)
        for msg_left in messages:
            ct_l = ore_encrypt_left(sk, msg_left)
            cmp_result = ore_compare(ct_l, ct_r)
            assert cmp_seq(msg_left, msg_right) == cmp_result