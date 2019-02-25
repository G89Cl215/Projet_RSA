generate_key(bits=512) = {
  p = nextprime(random(10^150));
  q = nextprime(random(10^150));
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

Fract_cont(x, y, res=[]) = {
  a = x \ y;
  res = concat(res, a);
  if(a * y == x, res, res = Fract_cont(y, x - a * y, res);res);

}
Fract_to_rational(l) = {
		     if(length(l) == 0, [0, 1]);
		     num = l[length(l)];
		     den = 1;
		     for(i=length(l) - 2, 0, num = l[i]*num+den;den = num);
		     [den, num];
		     }
  


Wiener_Attack(pub_key) = {
		       N = pub_key[1];
		       e = pub_key[2];
		       f = Fract_cont(e, N);
		       for(i = 1, length(f),);

}

Keys = generate_key();
key_pub = Keys[1];
key_priv = Keys[2];
N = key_pub[1];

message = [Mod(1, N), Mod(2, N), Mod(3,N), Mod(4, N)];
cyphered = encrypt(message, key_pub);
print("message de base = " lift(message));
print("message chiffré = " lift(cyphered));
print("message dechifre = " decrypt(cyphered, key_priv));
print(Fract_cont(e, n));
print(key_pub[1]);
print(Wiener_Attack(key_pub));