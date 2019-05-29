
Fract_cont(x, y, res=[]) =
{  \\ Donne le developpement en fractions_continues de x / y (Recurssive)
		a = x \ y;
		res = concat(res, a);
		if(a * y == x, res, res = Fract_cont(y, x - a * y, res);res);

}
Fract_to_rational(l) = { \\Transforme un developpement en fraction continues vers un rationnel
		if(length(l) == 0, [0, 1]);
		num = l[length(l)];
		den = 1;
		for(i=1,length(l) - 1, tmp = num;num = l[length(l) - i]*num+den;den=tmp);
		[num, den];
}

Fract_to_Reduites(l) = { \\ Donne la liste des reduites d un developpement en fractions continues
		RES = [];
		for(i = 2, length(l), RES = concat(RES, [Fract_to_rational(l[1..i])]));
		RES;
}

\\
\\
\\   implementation de l'attaque de Wiener
\\


Wiener_Attack_euclide_integre(pub_key) =
{
	\\Vecteur de test aléatoire avec des nombres > 10 et < 10^50	
	tester = [];
	for (i = 1, 10,
		tester = concat(tester, random(10^50) + 10));
	found = 0;
	quotient = pub_key[1]\pub_key[2];
	reste = pub_key[1]%pub_key[2];
	num = [quotient, quotient * quotient\reste + 1];
	denum = [1, quotient\reste];
	tmp = quotient\reste;
	reste = quotient%reste;
	quotient = tmp;
	while (reste > 2,

		tmp = quotient\reste;
		reste = quotient%reste;
		quotient = tmp;

		k = num[2]; 
		d = denum[2];         \\ K et D potentiels
		if ((pub_key[2] * d - 1) % k == 0,             \\k verifie bien le fait qu il soit un coeff de bezout
			phi = (e * d - 1) \ k;
			key_priv = [N, d];
			if (tester == decrypt(encrypt(tester, pub_key), key_priv),
				\\print("un bon k = ", k);
					print("phi = ", phi);
					somme = N - phi + 1;            \\ P + Q
					\\P et Q sont donnes par les racines du Polynome P_
					P_ = x^2 + somme * x + N;
					R = polroots(P_);
					P = floor(real(R[1]));
					Q = floor(real(R[2]));
					if(P * Q == N,
							print("key cracked");
							print("p = ", P);
							print("Q = ", Q));
							found = 1;
							break;
						 )
					 )
tmp = denum[2];			
denum[2] = quotient * denum[2] + denum[1];
denum[1] = tmp;
tmp = num[2];			
num[2] = quotient * num[2] + num[1];
num[1] = tmp;

);
	if(found == 1,
					d,
					0);
}
