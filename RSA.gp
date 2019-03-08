generate_key(bits=512) = {
  p = nextprime(random(2 ^ bits));
  q = nextprime(random(2 ^ bits));
  N = p * q;

  phi = (p-1)*(q-1);
  until(gcd(e,phi)==1, e = random(phi));
  d = e^-1 % phi;

  print("e = " e);
  print("d = "d);
  print("\n");
  print("N = "e * d);
  pub = [N, e];                                \\cle publique
  priv = [N, d];                               \\cle privee

  [pub, priv];
  }

generate_Wiener_key(bits=512) = { \\ 512 etant la taille de p et q (donc 1024 pour N)
  p = nextprime(random(2 ^ bits));
  q = nextprime(random(2 ^ bits));
  N = p * q;
  phi = (p-1)*(q-1);
  borne =  floor(1/3 * (2 ^ (bits/2))) * 10; \\Borne de l'Hypothese du thm de Wiener
  until(gcd(d,phi)==1 && d < borne, d = random(borne));  \\ On genere d abord d qui correspond au thm de wiener ensuite e
  \\while((gcd(d, phi) != 1 || d > borne), d = random(borne));
  e = d^-1 % phi;

  \\print("e = " e);
  \\print("d = "d);
  \\print("phi = " phi);
  \\print("\n");
  \\print("N = "e * d);
  pub = [N, e];                                \\cle publique
  priv = [N, d];                               \\cle privee
  [pub, priv];
  }



encrypt(message, pub_key) = {
  e = pub_key[2];
  N = pub_key[1];
  for(i = 1, length(message), message[i] =Mod(message[i] , N) ^ e);
  lift(message);
  }

decrypt(message, priv_key) = {
  d = priv_key[2];
  N = priv_key[1];
  for(i = 1, length(message), message[i] = Mod(message[i],N) ^ d);
  lift(message);
  }

\\ Fonctions necessaires pour l attaque de Wiener

Fract_cont(x, y, res=[]) = {  \\ Donne le developpement en fractions_continues de x / y (Recurssive)
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


Wiener_Attack(pub_key) = {

		       tester = [11, 2, 3, 4, 5, 6, 7, 8, 9, 10] ; \\Vecteur de test
		       found = 0;
		       N = pub_key[1];
		       e = pub_key[2];
		       f = Fract_cont(e, N);       \\Fractions continue de e/N
                       RED = Fract_to_Reduites(f); \\ Reduites de e/N
		       for(i = 1, length(RED),
                          k = RED[i][1]; d = RED[i][2];         \\ K et D potentiels
			  \\print("testing d = ", d);
                          if(k != 0,                           \\1 ere verification
                                 if((e * d - 1)%k == 0,             \\k verifie bien le fait qu il soit un coeff de bezout
				 phi = (e * d - 1)\k;
				 if((e * d) % phi == 1, \\inutile
				   key_priv = [N, d];
				   if(tester == decrypt(encrypt(tester, pub_key), key_priv),
		                     \\print("un bon k = ", k);
				   


                                   somme = N - phi + 1;            \\ P + Q
                                 \\Je developperais pour essayer d avoir p et q car ici on a la somme et le produit
                                   found = 1;
				   break;
           )
	   )
	   )
           )
           );
	   if(found == 1, d, 0);


}


Wiener_Attack_test(n=1000) = {
		     count = 0.0;
         gettime();
		     for(i = 1, n,
		         K = generate_Wiener_key();
		     	 D = K[2][2];
			 d = Wiener_Attack(K[1]);
			 if(d == D, print(d);print("d trouvé");count++)
			 );
         t = gettime() + 0.0;
         print("     \n bilan des attaques : \n\n");
		     print("    ", n, " attaques effectuees");
         print("    ", floor(count), " clefs privées trouvées");
		     print("    ", floor((count/n) * 100), "% taux reussite des attaques");
         print("    temps total ", floor(t), " ms");
         print("    ", floor(t/n), " ms/attaque");

		     }

\\Keys = generate_key();
\\key_pub = Keys[1];
\\key_priv = Keys[2];
\\N = key_pub[1];

\\message = [Mod(1, N), Mod(2, N), Mod(3,N), Mod(4, N)];
\\cyphered = encrypt(message, key_pub);
\\print("message de base = " lift(message));
\\print("message chiffré = " lift(cyphered));
\\print("message dechifre = " decrypt(cyphered, key_priv));
\\print(Fract_cont(e, n));
\\print(key_pub[1]);
\\print(Wiener_Attack(key_pub));
key = generate_Wiener_key();
pub_key = key[1];
l = Wiener_Attack(pub_key);
