\p 1000

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

generate_Wiener_key(bits=512, c=1) = { \\ 512 etant la taille de p et q (donc 1024 pour N)
  \\setrand(extern("echo $RANDOM"));
  until((p < q && q < 2 * p) || (q < p && p < 2 * q), 
  p = nextprime(random(2 ^ bits));
  q = nextprime(random(2 ^ bits)));
  N = p * q;
  phi = (p-1)*(q-1);
  borne =  floor(1/3 * (N ^ (1/4))) * c; \\Borne de l'Hypothese du thm de Wiener
                                            \\avec facteur c=100 -------> 2%
					    \\avec facteur c=50 -------> 4%
					    \\avec facteur c=10 -------> 20%
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

		       \\tester = [11, 2, 3, 4, 5, 6, 7, 8, 9, 10] ;
           \\Vecteur de test aléatoire avec des nombres > 10 et < 10^50
           tester = [];
           for(i = 1, 10, tester = concat(tester, random(10^50) + 10));
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
				                         print("phi = ", phi);
                                somme = N - phi + 1;            \\ P + Q
                                \\P et Q sont donnes par les racines du Polynome P_
                                P_ = x^2 + somme * x + N;
				                        R = polroots(P_);
				                        P = floor(real(R[1]));
				                        Q = floor(real(R[2]));
				                        if(P * Q == N, print("key cracked"); print("p = ", P);print("Q = ", Q));
                                found = 1;
				                        break;
                 )
	            )
	         )
        )
    );
	  if(found == 1, d, 0);


}


Wiener_Attack_test(n=1000, c=1) = {
        count = 0.0;
        gettime();
        for(i = 1, n,
		K = generate_Wiener_key(512, c);
		D = K[2][2];
	        d = Wiener_Attack(K[1]);
		if(d == D, print(d);print("d trouvé");count++, print("clef non trouvee");print(D))
			 );
         t = gettime() + 0.0;
	 res = floor((count/n) * 100);
         print("     \n bilan des attaques : \n\n");
		     print("    ", n, " attaques effectuees");
         print("    ", floor(count), " clefs privées trouvées");
		     print("    ", floor((count/n) * 100), "% taux reussite des attaques");
         print("    temps total ", floor(t), " ms");
         print("    ", floor(t/n), " ms/attaque");
	 res;
		     }


		     
\\
\\Partie Coppesmith
\\

G_u_v(P, N, u, v, m) = {
   G = N^(m-v) * x^u * P^v;
   G;	 
}


Coppersmith_Matrix(P, N, m=1) = {
       d = poldegree(P);
       eps = 1/2 * log(2)/log(N);
       X = floor(N^(1/d));
       u = 0;
       v = 0;
       CMP = 1;
       dim = d * (m+1);
       M = matrix(dim, dim);
       P_ = N;
       
       for(j = 1, m+1, for(i = 1, d, \\i = u, j = v 
       	     G = G_u_v(P, N, i-1, j-1, m);
	     \\print("u = ", j-1, " v = ", i-1);
	     G = subst(G, x, x*X);
	     V = Vecrev(Vec(G), dim);
	     for(k = 1, dim, M[CMP, k] = V[k]);
	     CMP++;
	   )
       );
       M_  = M~ * qflll(M~);
       M_ = M_~;
       \\M_  = qflll(M);
       DET = matdet(M);
       OMEGA = matrank(M);
       V = [];
       for(i = 1, matrank(M),
           for(j = 1, matrank(M),
	      V = concat(V, M_[matrank(M)-i+1, j]);
	   );
	   Q = Polrev(V);
	   Q_ = subst(Q, x, x/X);
	   \\if(Norme(V) < 2^(OMEGA/4) * DET ^ (1/OMEGA) , return(Polrev(V)));
	   if(Norme(V) < N^m / sqrt(OMEGA), return(Q_));
	   \\if(Norme(Vec(Q)) < N^m / sqrt(OMEGA), return(Q_));
	   V = []
	   );
	   
}

Coppersmith_2(P, N, m=1) = {
       d = poldegree(P);
       eps = 1/2 * log(2)/log(N);
       X = floor(N^(1/d));
       u = 0;
       v = 0;
       CMP = 1;
       dim = d * (m+1);
       M = matrix(dim, dim);
       P_ = N;
       
       for(j = 1, m+1, for(i = 1, d, \\i = u, j = v 
       	     G = G_u_v(P, N, i-1, j-1, m);
	     \\print("u = ", j-1, " v = ", i-1);
	     G = subst(G, x, x*X);
	     V = Vecrev(Vec(G), dim);
	     for(k = 1, dim, M[CMP, k] = V[k]);
	     CMP++;
	   )
       );
       M_  = M~ * qflll(M~);
       M_ = M_~;
       \\M_  = qflll(M);
       DET = matdet(M);
       OMEGA = matrank(M);
       V = [];
       for(i = 1, matrank(M),
           for(j = 1, matrank(M),
	      V = concat(V, M_[matrank(M)-i+1, j]);
	      );
	      Q = Polrev(V);
	      Q_ = subst(Q, x, x/X);
	      RACINES = floor(real(polroots(Q_)));
	      print(RACINES);
	      r = [];
	      for(i = 1, #RACINES, 
	          if(subst(P, x, RACINES[i]) % N == 0, 
	              print(RACINES[i]);
	              r = vecsort(r);
	              if(vecsearch(r, RACINES[i]) == 0, r = concat(r, RACINES[i]))
	              ));

	      V = []
	   );
	   return(r);
}


Norme(V) = {
  s = 0;
  for(i = 1, length(V),
    s += V[i]^2;
   );
  return(sqrt(s));
}

Norme_2(P, N) = {
  res = 0;
  X = N ^ (1/poldegree(P));
  l = Vecrev(P);
  for(i = 0, poldegree(P),
   res += (l[i+1] * X^i)^2;
  );
  return(sqrt(res));


}

small_roots(P, N) = {
  d = poldegree(P);
  X = N^(1/d);
  roots = [];
  

}

Wiener_Graph(x) = {
   y = [];
   for(i = 1, length(x), y = concat(y, Wiener_Attack_test(100, x[i])));
   plothrawexport("svg", x, y);
   plotdraw(0);
   y;
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
\\key = generate_Wiener_key();
\\pub_key = key[1];
\\l = Wiener_Attack(pub_key);
