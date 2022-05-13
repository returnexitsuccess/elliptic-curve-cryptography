# Elliptic Curve Cryptography
from Crypto.Hash import keccak
import random

class EC:
    # defines a Twisted Edwards curve
    # a x^2 + y^2 = 1 + d x^2 y^2 in finite field F_q
    def __init__(self, q, a, d):
        self.q = q
        self.a = a
        self.d = d
    
    # Modular multiplication a * b mod q
    def modMul(self, a, b):
        # a = a % self.q
        # r = 0
        # s = b
        # while a > 0:
        #     if a % 2 == 1:
        #         r = (r + s) % self.q
        #     s = (s + s) % self.q
        #     a = a // 2
        # return r
        return (a * b) % self.q
    
    # Modular exponentiation a^n mod q
    def modExp(self, a, n):
        # n = n % (self.q - 1)
        # r = 1
        # s = a
        # while n > 0:
        #     if n % 2 == 1:
        #         r = self.modMul(r, s)
        #     s = self.modMul(s, s)
        #     n = n // 2
        # return r
        return pow(a, n, self.q)
    
    # Modular inverse a^-1 = a^(q-1) mod q
    def modInv(self, a):
        return self.modExp(a, self.q-2)

    
    # Returns true if the point (x, y) is on the curve
    def onCurve(self, x, y):
        xsq = (x * x) % self.q
        ysq = (y * y) % self.q
        axsq = (self.a * xsq) % self.q
        dxsqysq = ( ( (self.d * xsq) % self.q) * ysq ) % self.q
        return (axsq + ysq - 1 - dxsqysq) % self.q == 0
    
    # Adds two points on the elliptic curve
    def addPoints(self, x1, y1, x2, y2):
        xnum = (self.modMul(x1, y2) + self.modMul(y1, x2)) % self.q
        xden = (1 + self.modMul(self.d, self.modMul(self.modMul(x1, x2), self.modMul(y1, y2)))) % self.q
        ynum = (self.modMul(y1, y2) - self.modMul(self.a, self.modMul(x1, x2))) % self.q
        yden = (1 - self.modMul(self.d, self.modMul(self.modMul(x1, x2), self.modMul(y1, y2)))) % self.q
        x = self.modMul(xnum, self.modInv(xden))
        y = self.modMul(ynum, self.modInv(yden))
        return (x, y)
    
    # Inverse of a point
    def pointInverse(self, x, y):
        return (-x % self.q, y % self.q)
    
    # Compute the multiple of a point nP, P = (x, y)
    def mulPoint(self, n, x, y):
        # R = 0
        Rx = 0
        Ry = 1

        # S = P
        Sx = x
        Sy = y

        while n > 0:
            if n % 2 == 1:
                (Rx, Ry) = self.addPoints(Rx, Ry, Sx, Sy)
            (Sx, Sy) = self.addPoints(Sx, Sy, Sx, Sy)
            n = n // 2
        return (Rx, Ry)

class Ed25519(EC):
    def __init__(self):
        self.q = pow(2, 255) - 19
        self.a = -1
        self.d = self.modMul(-121665 % self.q, self.modInv(121666))
        # Order of the curve is N = 2^c * l (l is prime)
        self.c = 3
        self.l = 7237005577332262213973186563042994240857116359379907606001950938285454250989

        # Base Point
        Gy = self.modMul(4, self.modInv(5))
        Gx, _ = self.decompressPoint(Gy)
        self.G = (Gx, Gy)
    
    # Point Compression (x, y) -> y with most significant bit 1 if x is odd
    def compressPoint(self, x, y):
        x = x % self.q
        if x % 2 == 1:
            y += pow(2, 255)
        return y
    
    # Point Decompression
    def decompressPoint(self, y):

        # Store most significant bit of y into b
        if y >= pow(2, 255):
            b = 1
            y -= pow(2, 255)
        else:
            b = 0
        
        u = (self.modMul(y, y) - 1) % self.q
        v = (self.modMul(self.d, self.modMul(y, y)) + 1) % self.q

        z = self.modMul(self.modMul(u, self.modExp(v, 3)), self.modExp(self.modMul(u, self.modExp(v, 7)), (self.q-5) // 8))

        vz2 = self.modMul(v, self.modExp(z, 2))

        if (vz2 - u) % self.q == 0:
            x = z
        elif (vz2 + u) % self.q == 0:
            x = self.modMul(z, self.modExp(2, (self.q-1)//4))
        else:
            # Should never be here
            raise AssertionError("Should not be here")

        if x % 2 != b:
            x = -x % self.q
        
        return (x, y)

class Key:
    def __init__(self, curve, privateKey=None):
        self.curve = curve

        if privateKey is None:
            self.privateKey = random.randint(1, curve.l - 1)
        else:
            self.privateKey = privateKey
        
        self.publicKey = curve.mulPoint(self.privateKey, curve.G[0], curve.G[1])
        self.publicKeyCompressed = curve.compressPoint(self.publicKey[0], self.publicKey[1])
    
    # Compute shared secret from other Public Key
    def sharedSecret(self, otherPublicKey):
        (x, y) = self.curve.decompressPoint(otherPublicKey)
        s = self.curve.mulPoint(self.privateKey, x, y)
        return self.curve.compressPoint(s[0], s[1])
    
    # Sign a message
    def sign(self, message):
        hk = int(keccak.new(data=self.privateKey.to_bytes(32, 'big'), digest_bits=256).hexdigest(), base=16)

        hash1 = keccak.new(digest_bits=256)
        hash1.update(hk.to_bytes(32, 'big'))
        hash1.update(message.encode('utf-8'))
        alpha = int(hash1.hexdigest(), base=16)

        aG = self.curve.mulPoint(alpha, self.curve.G[0], self.curve.G[1])
        aGcomp = self.curve.compressPoint(aG[0], aG[1])

        hash2 = keccak.new(digest_bits=256)
        hash2.update(aGcomp.to_bytes(32, 'big'))
        hash2.update(self.publicKeyCompressed.to_bytes(32, 'big'))
        hash2.update(message.encode('utf-8'))
        challenge = int(hash2.hexdigest(), 16)

        response = (alpha + challenge * self.privateKey) % (pow(2, self.curve.c) * self.curve.l)

        return (aGcomp, response)
    
    # Verify a signature
    def verify(self, aG, response, otherPublicKey, message):
        hash = keccak.new(digest_bits=256)
        hash.update(aG.to_bytes(32, 'big'))
        hash.update(otherPublicKey.to_bytes(32, 'big'))
        hash.update(message.encode('utf-8'))
        challenge = int(hash.hexdigest(), 16)

        rG = self.curve.mulPoint(pow(2, self.curve.c) * response, self.curve.G[0], self.curve.G[1])
        aGpoint = self.curve.decompressPoint(aG)
        multaG = self.curve.mulPoint(pow(2, self.curve.c), aGpoint[0], aGpoint[1])
        pubDecomp = self.curve.decompressPoint(otherPublicKey)
        chK = self.curve.mulPoint(pow(2, self.curve.c) * challenge, pubDecomp[0], pubDecomp[1])
        checkPoint = self.curve.addPoints(multaG[0], multaG[1], chK[0], chK[1])

        return (rG == checkPoint)

curve = Ed25519()
alice = Key(curve)
bob = Key(curve)
sa = alice.sharedSecret(bob.publicKeyCompressed)
sb = bob.sharedSecret(alice.publicKeyCompressed)
# print(f'{sa=}')
# print(f'{sb=}')
signature = alice.sign("my name is alice")
result = bob.verify(signature[0], signature[1], alice.publicKeyCompressed, "my name is alice")
print(result)

# keccak256 = int(keccak.new(data=(5).to_bytes(1, 'big'), digest_bits=256).hexdigest(), base=16)
# print(keccak256)