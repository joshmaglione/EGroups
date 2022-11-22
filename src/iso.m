//
//   Copyright 2022 Joshua Maglione, Mima Stanojkovski
//
//   Distributed under MIT License
//

import "construct.m" : __Ishitsuka_elliptic_rep, __Ishitsuka_elliptic_alt_map;
import "util.m" : __Outside_action, __Adj_module, __vector_to_matrix, __Elliptic_Autos;

// For a PCGrp G, return either (false, reason) or (maps, homotopism). The
// former is returned if G is not an E-group with a flex point. The latter is
// returned if G is an E-group with a flex point. The maps refer to the maps
// obtained from pCentralTensor, and the homotopism is the one obtained from
// TensorOverCentroid. 
__Extract_tensor := function(G)
    check, p, n := IsPrimePower(#G);
    if not check then 
        M := "Not a p-group."; 
        return false, M;
    elif p in {2, 3} then 
        M := "Prime must be different from 2 and 3.";
        return false, M;
    end if;
    if NilpotencyClass(G) ne 2 or Exponent(G) ne p then 
        M := "Not a p-class 2 group.";
        return false, M;
    end if;
    t, maps := pCentralTensor(G);
    if not IsFullyNondegenerate(t) then 
        M := "There are abelian direct factors.";
        return false, M; 
    end if;
    C := Centroid(t);
    if not IsCyclic(C) then 
        M := "The centroid of the p-central tensor is not a field.";
        return false, M;
    end if;
    s, H := TensorOverCentroid(t);
    if Dimension(Domain(s)[1]) ne 6 or Dimension(Codomain(s)) ne 3 then 
        M := "Pfaffian is not a cubic in three variables."; 
        return false, M;
    end if;
    Pf := Pfaffian(s);
    if not IsIrreducible(Pf) then 
        M := "Pfaffian is reducible.";
        return false, M;
    end if;
    PS := ProjectiveSpace(Parent(Pf));
    f := Curve(PS, Pf);
    if Genus(f) eq 0 then 
        M := "Pfaffian is a singular cubic"; 
        return false, M;
    end if;
    if #Points(Flexes(f)) eq 0 then 
        M := "The Pfaffian is a nonsingular cubic without flex points.";
        return false, M;
    end if;
    return maps, H;
end function;

// Given an E-tensor with a flex point, return the cohomotopism H such that the 
// Pfaffian of t @ H is a Weierstrass form and also return the Weierstrass 
// equation.
__Etensor_Weierstrass := function(t) 
    f := Pfaffian(t);
    PS := ProjectiveSpace(Parent(f));
    E, m1 := EllipticCurve(Curve(PS, f));
    EW, m2 := WeierstrassModel(E);
    H := __Outside_action(t, Transpose(Matrix(m1)*Matrix(m2))^-1);
    return H, EW; 
end function;

// Given an alternating tensor whose Pfaffian is irreducible, return the
// cohomotopism H such that t @ H is isotropically decomposable and also return 
// the type of the adjoint algebra. 
__isotropical_decomposition := function(t) 
    A := AdjointAlgebra(t);
    J := JacobsonRadical(A);
    if Dimension(J) gt 0 then 
        assert Dimension(J) eq 1;
        assert Dimension(A) eq 2;
        U := RowSpace(J.1);
        X := Matrix(ExtendBasis(Basis(U), Generic(U))); 
        type := "O";
    else 
        if SimpleParameters(A)[1][1] ne "unitary" then 
            if SimpleParameters(A)[1][1] eq "symplectic" then 
                type := "S";
                _, Symp, _, phi_inv := RecogniseClassicalSSA(A);
                B := Basis(Symp);
                I := [B[1] @ phi_inv, B[4] @ phi_inv];
            else 
                type := "X";
                // _, Exch, _, phi_inv := RecogniseExchangeSSA(A);
                // B := Basis(Exch);
                // print B;
                // I := [b @ phi_inv : b in B];
                I := PrimitiveIdempotents(A);
            end if;
            assert [x*(x @ Star(A)) : x in I] eq [A!0, A!0];
            U := RowSpace(I[1]);
            W := RowSpace(I[2]);
            assert Dimension(U meet W) eq 0;
            X := Matrix(Basis(U) cat Basis(W)); 
        else 
            X := IdentityMatrix(BaseRing(t), 6);
            type := "U";
        end if;
    end if;
    return Homotopism([*X, X, IdentityMatrix(BaseRing(t), 3)*], CohomotopismCategory(3)), type;
end function;

// Given an E-tensor whose Pfaffian defines a Weierstrass equation E, return 
// the cohomotopism H and a point P on E such that t @ H is equal to B_{E, P}.
__Normal_form := function(t, E)
    s := Tensor([ExtractBlock(X, 1, 4, 3, 3) : X in SystemOfForms(t)], 2, 1);
    // print Discriminant(s);
    Pts := Points(E);
    K := BaseRing(E);
    found := false;
    i := 1;
    print Sprintf("Searching through K-rational points (%o points).", #Pts); 
    while i le #Pts and not found do
        P := Pts[i]; 
        if P[3] ne 0 then 
            J := __Ishitsuka_elliptic_rep(E, P);
            A := __Adj_module(SystemOfForms(s), J); 
            if Dimension(A) gt 0 then 
                print "\tFound :", P;
                assert Dimension(A) eq 1;
                X, Y := __vector_to_matrix(A.1, 3, 3);
                assert IsInvertible(X) and IsInvertible(Y);
                found := true;
            end if;
        end if;
        i +:= 1;
    end while;
    Z := DiagonalJoin(X, Y^-1);
    return Homotopism([*Z, Z, IdentityMatrix(K, 3)*], CohomotopismCategory(3)), P;
end function; 

// Given an elliptic curve E, two points P and Q on E, and a matrix D, return
// the cohomotopism from B_{E, P} to B_{E, Q}, where the map on T is given by D.
__P_to_Q := function(E1, P, E2, Q, D)
    J_P := __Ishitsuka_elliptic_rep(E1, P);
    j := Tensor(J_P, 2, 1);
    J_Q := __Ishitsuka_elliptic_rep(E2, Q);
    H := __Outside_action(j, D);
    A := __Adj_module(SystemOfForms(j @ H), J_Q); 
    assert Dimension(A) eq 1;
    X, Y := __vector_to_matrix(A.1, 3, 3);
    assert IsInvertible(X) and IsInvertible(Y);
    M := DiagonalJoin(X, Y^-1);
    H := Homotopism([*M, M, D*], CohomotopismCategory(3));
    t1 := __Ishitsuka_elliptic_alt_map(E1, P, BaseRing(E1) : twist := false);
    t2 := __Ishitsuka_elliptic_alt_map(E2, Q, BaseRing(E2) : twist := false);
    assert t1 @ H eq t2;
    return H;
end function;

// Given elliptic curves E1 and E2 over K and points P1 and P2 on E1 and E2
// resp., determine all the pairs (X, sigma) in GL_3(K) x Gal(K/F_p) such that 
// there exists an isomorphism E1 --> sigma(E2) mapping P1 to sigma(P2) and the
// isomorphism is given by X. The element sigma is an integer from 
// {0, ..., e - 1}, where e is the degree of the extension. 
__Galois_elts := function(E1, P1, E2, P2: just_one:=false) 
    K := BaseRing(E1);
    p := Characteristic(K);
    e := Degree(K);
    j := jInvariant(E1);
    if not j in {K!0, K!1728} then 
        Omega := [K!(-1), K!1];
    else 
        R := PolynomialRing(K);
        if j eq K!1728 then 
            Omega := Roots(R.1^4 - 1);
        else 
            Omega := Roots(R.1^6 - 1);
        end if;
        Omega := [x[1] : x in Omega];
    end if;
    as := aInvariants(E2)[4..5];

    Gal_Aut := [];
    for i in [0..e - 1] do
        E2sig := EllipticCurve([a^(p^i) : a in as]);
        P2sig := E2sig![x^(p^i) : x in Eltseq(P2)];
        isiso, phi := IsIsomorphic(E1, E2sig);
        if isiso then 
            Q := P1 @ phi;
            S := {w : w in Omega | 
                P2sig[1] eq w^2*Q[1] and P2sig[2] eq w^3*Q[2]
            }; 
            for w in S do
                Append(~Gal_Aut, [*
                    i, 
                    __P_to_Q(E1, P1, E2sig, P2sig, 
                    (Matrix(phi)*DiagonalMatrix([w^2, w^3, 1]))^-1)
                *]);
                if just_one then 
                    return Gal_Aut;
                end if;
            end for;
        end if;
    end for; 

    return Gal_Aut;
end function;

__ETensor_iso := function(s_G, s_H)
    // Get the tensors into Weierstrass form.
    hmtp_G_W, E_G := __Etensor_Weierstrass(s_G);
    hmtp_H_W, E_H := __Etensor_Weierstrass(s_H);
    print E_G;
    print E_H; 
    // check, phi := IsIsomorphic(E_G, E_H);
    // H_iso := __Outside_action(s_G, Transpose(Matrix(phi)));
    t1 := s_G @ hmtp_G_W;
    t2 := s_H @ hmtp_H_W; //@ H_iso;
    print "Working with :", E_G;
    
    // Isotropically decompose the tensors.
    X1, Atype1 := __isotropical_decomposition(t1);
    X2, Atype2 := __isotropical_decomposition(t2);
    if Atype1 ne Atype2 then 
        print "Adjoint algebras are not isomorphic.";
        return []; 
    end if;
    if Atype1 eq "U" then 
        print "This sub-class of E-groups not implemented."; 
        return [];
    end if;
    if Atype1 eq "S" then 
        print "Adjoints of symplectic type.";
    else 
        print "Adjoints of exchange type.";
    end if;

    // Write the tensors in normal form, using J_{E, P}. 
    toJP1, P1 := __Normal_form(t1 @ X1, E_G);
    toJP2, P2 := __Normal_form(t2 @ X2, E_H); 

    // Get a suitable (Galois element, isomorphism) pair. 
    Gal_Aut := __Galois_elts(E_G, P1, E_H, P2 : just_one:=true);
    if #Gal_Aut eq 0 then 
        print "There is no suitable (Galois element, isomorphism) pair between marked elliptic curves.";
        return [];
    end if; 
    alpha := Integers()!(Gal_Aut[1][1]);

    // P_to_Q := __P_to_Q(E_G, P1, Gal_Aut[1][4], Gal_Aut[1][3]); 

    V := Domain(s_G)[1];
    T := Codomain(s_G);
    p := Characteristic(BaseRing(V));
    BOT1 := map< V -> V | 
        x :-> x*(Gal_Aut[1][2].2*toJP1.2*X1.2*hmtp_G_W.2)^-1 
    >; 
    BOT_Gal := map< V -> V | 
        x :-> V![y^(Integers()!(p^alpha)) : y in Eltseq(x)] 
    >;
    BOT2 := map< V -> V | 
        x :-> x*(toJP2.2*X2.2*hmtp_H_W.2) 
    >;
    F := BOT1*BOT_Gal*BOT2;
    TOP1 := map< T -> T | 
        x :-> x*(hmtp_H_W.0*X2.0*toJP2.0) 
    >;
    TOP_Gal := map< T -> T | 
        x :-> T![y^(Integers()!(p^alpha)) : y in Eltseq(x)] 
    >;
    TOP2 := map< T -> T | 
        x :-> x*(hmtp_G_W.0*X1.0*toJP1.0*Gal_Aut[1][2].0)^-1 
    >;
    G := TOP1*TOP_Gal*TOP2;
    final_hom := Homotopism([*F, F, G*], CohomotopismCategory(3));
    // assert s_H @ final_hom eq s_G;
    return [final_hom];
end function;

intrinsic EGIsIsomorphic(G::GrpPC, H::GrpPC) -> BoolElt, Map 
{Decide if the two E-groups G and H are isomorphic, and if so return an isomorphism.}
    if #G ne #H then 
        print "Groups have different order.";
        return false, _; 
    end if;
    Gmaps, Ghmtp := __Extract_tensor(G);
    Hmaps, Hhmtp := __Extract_tensor(H);
    require Type(Hmaps) ne BoolElt or Type(Gmaps) ne BoolElt : "Both groups are not E-groups.";
    if Type(Hmaps) eq BoolElt or Type(Gmaps) eq BoolElt then 
        print "One group is an E-group, but the other is not.";
        return false, _;  
    end if;
    s_G := Codomain(Ghmtp);
    s_H := Codomain(Hhmtp);
    dat := __ETensor_iso(s_G, s_H);
    if #dat eq 0 then 
        return false, _;
    end if;
    X := dat[1].2;

    out := function(x) 
        return ((((x @ Gmaps[1]) @ Ghmtp.2) @ X) @@ Hhmtp.2) @@ Hmaps[1];
    end function;
    im := [<x, out(x)> : x in PCGenerators(G) | not x in DerivedSubgroup(G)]; 
    return true, hom< G -> H | im >;
end intrinsic;
