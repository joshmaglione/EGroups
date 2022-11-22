//
//   Copyright 2022 Joshua Maglione, Mima Stanojkovski
//
//   Distributed under MIT License
//


// Given a tensor t and a linear map Z, construct the (co-)homotopism given by
// (id, id, Z). 
__Outside_action := function(t, Z)
    K := BaseRing(t);
    n := Dimension(Domain(t)[1]);
    M := [*IdentityMatrix(K, n), IdentityMatrix(K, n), Z*];
    return Homotopism(M, CohomotopismCategory(3)); 
end function;

// Taken from Auto-Sandbox
// Given sequences of matrices formsA and formsB, return the adjoint module 
// Adj(formsA, formsB). 
__Adj_module := function( formsA, formsB )
	c := #formsA;
	a := Nrows(formsB[1]);
	b := Ncols(formsA[1]);
	K := BaseRing(formsA[1]);

	s := Nrows(formsA[1]);
	t := Ncols(formsB[1]);

	A := formsA[1];
	for i in [2..c] do
		A := HorizontalJoin(A, formsA[i]);
	end for;

	mat := ZeroMatrix( K, a*s+t*b, a*b*c );
	for j in [1..a] do
		InsertBlock(~mat, A, s*(j-1)+1, b*c*(j-1)+1 );
	end for;

	delete A;

	slicedforms := [ [ ExtractBlock(-Transpose(B), 1, i, t, 1) : i in [1..a]] : B in formsB ];
	for i in [1..a] do
		for j in [1..c] do
			for k in [1..b] do
				InsertBlock(~mat, slicedforms[j][i], t*(k-1)+a*s+1, c*b*(i-1)+b*(j-1)+k );
			end for;
		end for;
	end for;
	delete slicedforms;
	
	return Nullspace(mat);
end function;

// Given a vector x and positive integers a and b, return two matrices, the 
// first a x a and the second b x b. This assumes #x is at least a^2 + b^2. 
__vector_to_matrix := function(x,a,b)
	X := Matrix(BaseRing(x), a,a, Eltseq(x)[1..(a^2)]);
	Y := Matrix(BaseRing(x), b,b, Eltseq(x)[(a^2+1)..(a^2+b^2)]);
	return X,Y;
end function;

// Given an elliptic curve over a field K of characteristic not equal to 2 or 3,
// return the list [w : w in K] such that (x, y) |-> (w^2x, w^3y) induces an
// automorphism.
__Elliptic_Autos := function(E)
    K := BaseRing(E);
    assert not Characteristic(K) in {2, 3};
    if not jInvariant(E) in {K!0, K!1728} then 
        Omega := [K!(-1), K!1];
    else 
        R := PolynomialRing(K);
        if jInvariant(E) eq K!1728 then 
            Omega := Roots(R.1^4 - 1);
        else 
            Omega := Roots(R.1^6 - 1);
        end if;
        Omega := [x[1] : x in Omega];
    end if;
    return Omega;
end function;
