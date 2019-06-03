setrand(extern("echo $RANDOM"));
\p 10000

generate_Wiener_key(bits = 512, c = 1) =
{ \\ 512 etant la taille de p et q (donc 1024 pour N)
		until((p < q && q < 2 * p) || (q < p && p < 2 * q), 
						p = nextprime(random(2 ^ bits));
						q = nextprime(random(2 ^ bits)));
		N = p * q;
		phi = (p-1)*(q-1);
		borne =  floor(1/3 * (N ^ (1/4))) * c; \\Borne de l'Hypothese du thm de Wiener
		until(gcd(d,phi)==1 && d < borne,
			d = random(borne));  \\ On genere d abord d qui correspond au thm de wiener ensuite e
				\\while((gcd(d, phi) != 1 || d > borne), d = random(borne));
		e = d^-1 % phi;
		pub = [N, e];                                \\cle publique
		priv = [N, d];                               \\cle privee
		[pub, priv];
}

Wiener_Attack_euclide_integre(pub_key) =
{
	found = 0;
	step = 0;
	quotient = [e\N, 0];
	reste = [e % N, 0];
	quotient[2] = N \ reste[1];
	reste[2] = N % reste[1];
	print(reste);
	num = [quotient[1], quotient[1] * quotient[2] + 1];
	denum = [1, quotient[2]];
	while (reste[2] > 0,
		k = num[2];
		d = denum[2];
		if ((e * d - 1) % k == 0,             \\k verifie bien le fait qu il soit un coeff de bezout
			phi = (e * d - 1) \ k;
			key_priv = [N, d];
			somme = N - phi + 1;            \\ P + Q
			P_ = x^2 - somme * x + N;
			R = polroots(P_);step = step + 1;
			P = floor(real(R[2]));
			Q = floor(real(R[1]));
			if (P * Q == N,
				print("key cracked");
				print("P_déchiffré = ", P);
				print("Q_déchiffré = ", Q);
				found = 1;
				break));
			quotient = [quotient[2], reste[1] \reste[2]];
			reste = [reste[2], reste[1] % reste[2]];
			denum = [denum[2], quotient[2] * denum[2] + denum[1]];
			num = [num[2], quotient[2] * num[2] + num[1]];
			);
	if (found == 1,
			d,
			0);
}


key = generate_Wiener_key();
pub_key = key[1];
l = Wiener_Attack_euclide_integre(pub_key);
