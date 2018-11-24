#include<iostream>
#include<string>
#include<iomanip>
#include<vector>
#include<ctime>
#include<tuple>
#include<utility>
#include<cmath>
#include "sha256.h"
#pragma once

typedef unsigned int uint;

using namespace std;

std::string to_hex(uint value);
uint F(uint X, uint Y, uint Z);
uint G(uint X, uint Y, uint Z);
uint H(uint X, uint Y, uint Z);
uint I(uint X, uint Y, uint Z);
uint rotate_left(uint value, int shift);
std::string get_md5(std::string in);

int64_t hashToDec(const string& md5)
{
	vector<char> convertTable;
	convertTable.push_back('*');
	convertTable.push_back('*');

	for (int i = static_cast<int>('0'); i <= static_cast<int>('9'); i++)
	{
		convertTable.push_back(static_cast<char>(i));
	}

	for (int i = static_cast<int>('A'); i <= static_cast<int>('Z'); i++)
	{
		convertTable.push_back(static_cast<char>(i));
	}

	for (int i = static_cast<int>('a'); i <= static_cast<int>('z'); i++)
	{
		convertTable.push_back(static_cast<char>(i));
	}

	int64_t answer = 1;
	int step = 1;
	for (const char& c : md5)
	{
		for (int i = 0; i < convertTable.size(); i++)
		{
			if (c == static_cast<char>(convertTable[i]))
			{
				answer += i ^ step;
				step++;
				break;
			}
		}
	}

	return answer;
}

bool isPrime(const int64_t& n)
{
	for (size_t i = 2; i <= n / 2; ++i)
	{
		if (n % i == 0)
		{
			return false;
		}
	}
	return true;
}

pair<int64_t, int64_t> setPrimePair()
{
	pair<int64_t, int64_t> result;
	int64_t p = 2 + rand();
	int64_t q = 2 + rand();

	while (!isPrime(p) || !isPrime(q) || q == p)
	{
		p = 2 + rand();
		q = 2 + rand();
	}

	result.first = p;
	result.second = q;
	return result;
}

int64_t rev(int64_t e, int64_t ejler)
{
	if (e == 1)
	{
		return 1;
	}
	return (1 - rev(ejler%e, e) * ejler) / e + ejler;
}

int getAlphbetCode(const char& c)
{
	int iter = 0;
	for (int i = 'a'; i <= 'z'; i++)
	{
		iter++;
		if (c == static_cast<char>(i))
		{
			return iter;
		}
	}

	return -1;
}

char getAlphbetSymbol(const int& num)
{
	for (int i = 'a'; i <= 'z'; i++)
	{
		if (num + 96 == i)
		{
			return static_cast<char>(i);
		}
	}

	return '_';
}

tuple<int64_t, int64_t, int64_t> cipherRSA()
{
	int64_t p = 0;
	int64_t q = 0;
	tie(p, q) = setPrimePair();
	int64_t n = p * q;
	int64_t ejler = (p - 1)*(q - 1);
	int64_t e = 2 + rand() % ejler;
	while (!isPrime(e))
	{
		e = 2 + rand() % ejler;
	}
	// count secret key e*d mod ejler = 1
	int64_t d = rev(e, ejler);

	//check is d correct;
	//int64_t c = (e*d) % ejler;

	return { e,d,n };
}

int64_t cdn(int64_t c, int64_t d, int64_t n)      // work out c^d mod n
{
	int64_t value = 1;
	while (d > 0)
	{
		value *= c;
		value %= n;
		d--;
	}
	return value;
}

int64_t rsaCreateDigitalSignature(const int64_t& decMd5, const int64_t& secretKey,const int64_t& n)
{
	return cdn(decMd5, secretKey, n);
}

bool rsaMessageConfimatioin(const string& message, const int64_t& AdecMd5, const int64_t& digitalSignature, const int64_t& openKey, const int64_t& n)
{
	int64_t BdecMd5 = cdn(digitalSignature,openKey,n);
	if (BdecMd5 == AdecMd5)
	{
		return true;
	}

	return false;
}

int countBits(int number)
{
	return static_cast<int>(log2(number) + 1);
}

tuple<int64_t, int64_t, int64_t, int64_t, int64_t> cipherGost34()
{
	int64_t p = 79;
	int64_t q = 13;
	int64_t a = rand() % (p - 1);
	while (cdn(a, q, p) != 1)
	{
		a = rand() % (p - 1);
	}
	int64_t x = rand() % (q - 1);
	int64_t y = cdn(a,x,p);

	return {p,q,a,x,y};
}

tuple<int64_t, int64_t> createGost34DigitalSignature(const string& message, const int64_t p, const int64_t& q, const int64_t& a, const int64_t& x)
{
	int64_t h = hashToDec(sha256(message));
	int64_t k = rand() % (q - 1);

	int64_t w1 = cdn(a, k, p);
	int64_t w2 = w1 % p;
	while (w2 == 0)
	{
		k = rand() % (q - 1);
		w1 = cdn(a, k, p);
		w2 = w1 % p;
	}

	int64_t s = (x*w2 + k * h);
	while (s == 0)
	{
		k = rand() % (q - 1);
		w1 = cdn(a, k, p);
		w2 = w1 % p;
		s = (x*w2 + k * h);
	}

	return { w2,s };
}

bool gost34MessageConfirmation(const string& message, const int64_t& decSha256, const int64_t& p, const int64_t& q, const int64_t& a, const int64_t& y, const int64_t& w2, const int64_t& s)
{
	int64_t BdecSha256 = hashToDec(sha256(message));
	int64_t v = cdn(BdecSha256, (q - 2), q);
	int64_t z1 = (s*v) % q;
	int64_t z2 = ((q - w2)*v) % q;

	int64_t u = ((static_cast<int64_t>(pow(a, z1)*pow(y, z2))) % p) % q;
	if (w2 == u)
	{
		return true;
	}

	return false;
}

tuple<int64_t, int64_t> createGost2001DigitalSignature(const string& message, const int& )
{
	int64_t h = hashToDec(sha256(message));

}

void main()
{
	string message = "podanenko";
	/*int64_t openKey, secretKey, n;
	tie(openKey, secretKey, n) = cipherRSA();

	int64_t sRsa = rsaCreateDigitalSignature(hashToDec(get_md5(message)), secretKey, n);*/
	int64_t p, q, a, x, y;
	tie(p, q, a, x, y) = cipherGost34();

	int64_t w2, s;
	tie(w2,s) = createGost34DigitalSignature(message,p,q,a,x);

	cout << gost34MessageConfirmation(message,hashToDec(sha256(message)),p,q,a,y,w2,s) << endl;
	
	system("pause");
}

std::string to_hex(uint value)
{
	std::string out;
	unsigned char hex;
	char hex_res[3];
	while (value)
	{
		hex = value % 256;
		_itoa_s(hex, hex_res, 16);
		if (hex_res[1] == '\0')
		{
			hex_res[1] = hex_res[0];
			hex_res[0] = '0';
			hex_res[2] = '\0';
		}
		out.append(hex_res);
		value /= 256;
	}
	return out;
}

uint F(uint X, uint Y, uint Z)
{
	return ((X & Y) | ((~X) & Z));
}

uint G(uint X, uint Y, uint Z)
{
	return (X & Z) | (Y & (~Z));
}

uint H(uint X, uint Y, uint Z)
{
	return X ^ Y ^ Z;
}

uint I(uint X, uint Y, uint Z)
{
	return Y ^ (X | (~Z));
}

uint rotate_left(uint value, int shift)
{
	return value << shift | value >> (32 - shift);
}

std::string get_md5(std::string in)
{
	int length = in.length(); //получаем длину входного сообщения. 
	int rest = length % 64; //остаток от деления на 64байта. 
	int size = 0; //тут будет храниться размер сообщения после первых 2ух шагов.

				  //Шаг 1.
	if (rest < 56) //если остаток от деления на 64 меньше 56
		size = length - rest + 56 + 8; //подгоняем размер так, что бы он был кратен 64(+8 байт для 2ого шага).
	else //иначе (если остаток больше 56)
		size = length + 64 - rest + 56 + 8; //подгоняем размер так, что бы он был кратен 64(+8 байт для 2ого шага).

	unsigned char *msg_for_decode = new unsigned char[size]; //создаем динамический массив для хранения сообщения, которое далее будет кодироваться

	for (int i = 0; i < length; i++) //первые length элементов сIn
		msg_for_decode[i] = in[i]; //заполняем символами входного сообщения

	msg_for_decode[length] = 0x80; //ставим в конец сообщения единичный бит.

	for (int i = length + 1; i < size; i++) //а все остальное
		msg_for_decode[i] = 0; //заполняем нулями

							   //Шаг 2.
	__int64 bit_length = (uint)(length) * 8; //длина сообщения в битах.

	for (int i = 0; i < 8; i++) //последние 8 байт
		msg_for_decode[size - 8 + i] = (unsigned char)(bit_length >> i * 8); //заполняем 64-битным представлением длины данных до выравнивания

																			 //Шаг 3.
	uint A = 0x67452301, B = 0xefcdab89, C = 0x98badcfe, D = 0x10325476; //Инициализируем начальные значения регистров.
	uint T[64]; //64-элементная таблица данных (констант).

	for (int i = 0; i<64; i++) //всю таблицу констант
		T[i] = uint(pow(2, 32)*fabs(sin(i + 1)));; //заполняем в соответствии с алгоритмом.

												   //объявляем массив Х, в котором будет 32-разрядное представление сообщения.
	uint *X = (uint*)(msg_for_decode); //загоняем в массив Х сообщение msg_for_decode.

									   //Шаг 4.
	uint AA, BB, CC, DD;

	for (int i = 0; i < size / 4; i += 16)
	{
		AA = A; BB = B; CC = C; DD = D;
		
		//раунд 1
		A = B + rotate_left((A + F(B, C, D) + X[i + 0] + T[0]), 7);
		D = A + rotate_left((D + F(A, B, C) + X[i + 1] + T[1]), 12);
		C = D + rotate_left((C + F(D, A, B) + X[i + 2] + T[2]), 17);
		B = C + rotate_left((B + F(C, D, A) + X[i + 3] + T[3]), 22);

		A = B + rotate_left((A + F(B, C, D) + X[i + 4] + T[4]), 7);
		D = A + rotate_left((D + F(A, B, C) + X[i + 5] + T[5]), 12);
		C = D + rotate_left((C + F(D, A, B) + X[i + 6] + T[6]), 17);
		B = C + rotate_left((B + F(C, D, A) + X[i + 7] + T[7]), 22);

		A = B + rotate_left((A + F(B, C, D) + X[i + 8] + T[8]), 7);
		D = A + rotate_left((D + F(A, B, C) + X[i + 9] + T[9]), 12);
		C = D + rotate_left((C + F(D, A, B) + X[i + 10] + T[10]), 17);
		B = C + rotate_left((B + F(C, D, A) + X[i + 11] + T[11]), 22);

		A = B + rotate_left((A + F(B, C, D) + X[i + 12] + T[12]), 7);
		D = A + rotate_left((D + F(A, B, C) + X[i + 13] + T[13]), 12);
		C = D + rotate_left((C + F(D, A, B) + X[i + 14] + T[14]), 17);
		B = C + rotate_left((B + F(C, D, A) + X[i + 15] + T[15]), 22);
		//раунд 2
		A = B + rotate_left((A + G(B, C, D) + X[i + 1] + T[16]), 5);
		D = A + rotate_left((D + G(A, B, C) + X[i + 6] + T[17]), 9);
		C = D + rotate_left((C + G(D, A, B) + X[i + 11] + T[18]), 14);
		B = C + rotate_left((B + G(C, D, A) + X[i + 0] + T[19]), 20);

		A = B + rotate_left((A + G(B, C, D) + X[i + 5] + T[20]), 5);
		D = A + rotate_left((D + G(A, B, C) + X[i + 10] + T[21]), 9);
		C = D + rotate_left((C + G(D, A, B) + X[i + 15] + T[22]), 14);
		B = C + rotate_left((B + G(C, D, A) + X[i + 4] + T[23]), 20);

		A = B + rotate_left((A + G(B, C, D) + X[i + 9] + T[24]), 5);
		D = A + rotate_left((D + G(A, B, C) + X[i + 14] + T[25]), 9);
		C = D + rotate_left((C + G(D, A, B) + X[i + 3] + T[26]), 14);
		B = C + rotate_left((B + G(C, D, A) + X[i + 8] + T[27]), 20);

		A = B + rotate_left((A + G(B, C, D) + X[i + 13] + T[28]), 5);
		D = A + rotate_left((D + G(A, B, C) + X[i + 2] + T[29]), 9);
		C = D + rotate_left((C + G(D, A, B) + X[i + 7] + T[30]), 14);
		B = C + rotate_left((B + G(C, D, A) + X[i + 12] + T[31]), 20);

		//раунд 3
		A = B + rotate_left((A + H(B, C, D) + X[i + 5] + T[32]), 4);
		D = A + rotate_left((D + H(A, B, C) + X[i + 8] + T[33]), 11);
		C = D + rotate_left((C + H(D, A, B) + X[i + 11] + T[34]), 16);
		B = C + rotate_left((B + H(C, D, A) + X[i + 14] + T[35]), 23);

		A = B + rotate_left((A + H(B, C, D) + X[i + 1] + T[36]), 4);
		D = A + rotate_left((D + H(A, B, C) + X[i + 4] + T[37]), 11);
		C = D + rotate_left((C + H(D, A, B) + X[i + 7] + T[38]), 16);
		B = C + rotate_left((B + H(C, D, A) + X[i + 10] + T[39]), 23);
		
		A = B + rotate_left((A + H(B, C, D) + X[i + 13] + T[40]), 4);
		D = A + rotate_left((D + H(A, B, C) + X[i + 0] + T[41]), 11);
		C = D + rotate_left((C + H(D, A, B) + X[i + 3] + T[42]), 16);
		B = C + rotate_left((B + H(C, D, A) + X[i + 6] + T[43]), 23);

		A = B + rotate_left((A + H(B, C, D) + X[i + 9] + T[44]), 4);
		D = A + rotate_left((D + H(A, B, C) + X[i + 12] + T[45]), 11);
		C = D + rotate_left((C + H(D, A, B) + X[i + 15] + T[46]), 16);
		B = C + rotate_left((B + H(C, D, A) + X[i + 2] + T[47]), 23);
	
		//раунд 4
		A = B + rotate_left((A + I(B, C, D) + X[i + 0] + T[48]), 6);
		D = A + rotate_left((D + I(A, B, C) + X[i + 7] + T[49]), 10);
		C = D + rotate_left((C + I(D, A, B) + X[i + 14] + T[50]), 15);
		B = C + rotate_left((B + I(C, D, A) + X[i + 5] + T[51]), 21);

		A = B + rotate_left((A + I(B, C, D) + X[i + 12] + T[52]), 6);
		D = A + rotate_left((D + I(A, B, C) + X[i + 3] + T[53]), 10);
		C = D + rotate_left((C + I(D, A, B) + X[i + 10] + T[54]), 15);
		B = C + rotate_left((B + I(C, D, A) + X[i + 1] + T[55]), 21);

		A = B + rotate_left((A + I(B, C, D) + X[i + 8] + T[56]), 6);
		D = A + rotate_left((D + I(A, B, C) + X[i + 15] + T[57]), 10);
		C = D + rotate_left((C + I(D, A, B) + X[i + 6] + T[58]), 15);
		B = C + rotate_left((B + I(C, D, A) + X[i + 13] + T[59]), 21);

		A = B + rotate_left((A + I(B, C, D) + X[i + 4] + T[60]), 6);
		D = A + rotate_left((D + I(A, B, C) + X[i + 11] + T[61]), 10);
		C = D + rotate_left((C + I(D, A, B) + X[i + 2] + T[62]), 15);
		B = C + rotate_left((B + I(C, D, A) + X[i + 9] + T[63]), 21);

		A += AA;
		B += BB;
		C += CC;
		D += DD;
	}

	delete[]msg_for_decode; //не забываем освободить память =)
							//Шаг 5.
	std::string res = to_hex(A) + to_hex(B) + to_hex(C) + to_hex(D); //заполняем выходную строку hex-//представлением, полученных в шаге 4, регистров.

	return res; //возвращаем строку с хеш-кодом.
}