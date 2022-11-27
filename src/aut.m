//
//   Copyright 2022 Joshua Maglione
//
//   Distributed under MIT License
//

import "construct.m" : __Ishitsuka_elliptic_rep, __Ishitsuka_elliptic_alt_map;
import "iso.m" : __Extract_tensor, __Etensor_Weierstrass, __isotropical_decomposition, __Normal_form, __Galois_elts;
import "util.m" : __Adj_module, __vector_to_matrix, __Outside_action;

__Lift_Symplectic := function(E, P) 
    K := BaseRing(E);
    t := __Ishitsuka_elliptic_alt_map(E, P, K : twist:=false);
    A := AdjointAlgebra(t);
    _, S, phi, phi_inv := RecogniseClassicalSSA(A);
    gens := [];
    for g in Generators(GL(2, K)) do
        X := (S!g) @ phi_inv;
        d := Determinant(g)^-1;
        Append(~gens, Homotopism([*X, X, d*IdentityMatrix(K, 3)*], CohomotopismCategory(3))); 
        // assert t @ (gens[#gens]) eq t; 
    end for;
    return gens; 
end function;

__Lift_Exchange := function(E, P) 
    K := BaseRing(E);
    t := __Ishitsuka_elliptic_alt_map(E, P, K : twist:=false);
    X0 := DiagonalMatrix([-1, K!1, 1]);
    M := Matrix(K, 2, 2, [0, 1, 1, 0]);
    X := KroneckerProduct(M, X0);
    Z := DiagonalMatrix([-1, K!1, -1]);
    H := Homotopism([*X, X, Z*], CohomotopismCategory(3));
    a := PrimitiveElement(K);
    I := IdentityMatrix(K, 3);
    A := a*I;
    gens := [
        H, Homotopism([*DiagonalJoin(A, I), DiagonalJoin(I, A), A*], 
        CohomotopismCategory(3)), Homotopism([*DiagonalJoin(I, A), DiagonalJoin(A, I), A*], CohomotopismCategory(3))
    ];
    assert t @ H eq t; 
    return gens;
end function;

__Lift_Outer := function(E, P, Z) 
    Forms := __Ishitsuka_elliptic_rep(E, P);
    t := Tensor(Forms, 2, 1); 
    H := __Outside_action(t, Z);
    A := __Adj_module(SystemOfForms(t @ H), Forms);
    assert Dimension(A) eq 1;
    X, Y := __vector_to_matrix(A.1, 3, 3);
    M := DiagonalJoin(X, Y^-1);
    return Homotopism([*M, M, Z*], CohomotopismCategory(3));
end function;

__Matrix_Translation := function(E, T)
    K := BaseRing(E);
    V := VectorSpace(K, 3);
    if #K le 20 then 
        xpts := K;
    else 
        xpts := [Random(K) : i in [1..20]];
    end if;
    pts := &cat[Points(E, x) : x in xpts];
    aff_pts := [V!Eltseq(p) : p in pts];
    if RowSpace(Matrix(aff_pts)) ne V then // If not enough points, just extend
        L := GF(Characteristic(K)^(2*Degree(K)));
        E_L := EllipticCurve([L!x : x in aInvariants(E)]);
        P_L := E_L!(Identity(E) @ T);
        T_L := TranslationMap(E_L, P_L);
        return Matrix(K, 3, 3, Eltseq($$(E_L, T_L)));
    end if;
    Z := ZeroMatrix(K, 3*#pts, 9 + #pts); 
    for i in [1..#pts] do
        InsertBlock(~Z, KroneckerProduct(IdentityMatrix(K, 3), Matrix(aff_pts[i])), (i-1)*3 + 1, 1);
        InsertBlock(~Z, Transpose(Matrix(V!Eltseq(pts[i] @ T))), (i-1)*3 + 1, 9 + i);
    end for;
    N := NullspaceOfTranspose(Z);
    assert Dimension(N) gt 0;
    T_lin := Transpose(Matrix(K, 3, 3, Eltseq(N.1)[1..9]));
    // assert forall{x : x in pts | V!Eltseq(x @ T) in sub<V | (V!Eltseq(x))*T_lin>}; 
    return Transpose(T_lin);
end function;

intrinsic EGAutomorphismGroup(G::GrpPC) -> GrpAuto
{Returns the automorphism group of the decomposable E-group G.}
    Gmaps, Ghmtp := __Extract_tensor(G);
    require Type(Gmaps) ne BoolElt : "Given group is not an E-group.";
    s := Codomain(Ghmtp);
    hmtp_W, E := __Etensor_Weierstrass(s);
    K := BaseRing(E);
    t := s @ hmtp_W; 
    X, Atype := __isotropical_decomposition(t);
    require Atype ne "U" : "This sub-class of E-groups not implemented."; 
    toJP, P := __Normal_form(t @ X, E);
    t_norm := t @ X @ toJP;
    if Atype eq "S" then 
        print "Adjoints of symplectic type.";
        adj_gens := __Lift_Symplectic(E, P); 
        ord_adj := (#K + 1)*(#K - 1)^2*#K;
    else 
        print "Adjoints of exchange type.";
        adj_gens := __Lift_Exchange(E, P); 
        ord_adj := 2*(#K - 1)^2;
    end if;
    // assert forall{H : H in adj_gens | t_norm @ H eq t_norm};

    Gal_Aut := __Galois_elts(E, P, E, P);
    ord_stab := #Gal_Aut;
    // Syl3, phi := pPowerTorsion(E, 3); // This is not optimized for 3-tor
    // if #Syl3 eq 1 then 
    //     E3 := Syl3;
    // else 
    //     E3 := Omega(Syl3, 1);
    // end if;
    E3 := Points(Flexes(E));
    ord_3 := #E3;

    pseudo_gens := adj_gens;
    for Q in E3 diff {@E![0,1,0]@} do 
        tau_Q := TranslationMap(E, Q);
        Append(~pseudo_gens, __Lift_Outer(E, P, __Matrix_Translation(E, tau_Q)));
    end for;
    // assert forall{H : H in pseudo_gens | t_norm @ H eq t_norm};
    
    mat_to_map := func< V, M | map< V -> V | x :-> x*M > >;
    p := Characteristic(K);
    t_G := Domain(Ghmtp); 
    V := Domain(t_G)[1];
    V_K := Domain(s)[1];
    W := Codomain(t_G);
    W_K := Codomain(s);
    gens_V := [*
        mat_to_map(V_K, (toJP.2*X.2*hmtp_W.2)^-1*g.2*toJP.2*X.2*hmtp_W.2) : g in pseudo_gens
    *];
    gens_W := [*
        mat_to_map(W_K, hmtp_W.0*X.0*toJP.0*g.0*(hmtp_W.0*X.0*toJP.0)^-1) : g in pseudo_gens
    *];
    Gal_vec := func< V, a | 
        map< V -> V | x :-> V![u^(p^a) : u in Eltseq(x)] >
    >;
    for dat in Gal_Aut do
        alpha := dat[1];
        BOT1 := map< V_K -> V_K | 
            x :-> x*(dat[2].2*toJP.2*X.2*hmtp_W.2)^-1
        >; 
        BOT2 := map< V_K -> V_K | 
            x :-> x*(toJP.2*X.2*hmtp_W.2) 
        >;
        Append(~gens_V, BOT1*Gal_vec(V_K, Degree(K) - alpha)*BOT2);
        TOP1 := map< W_K -> W_K | 
            x :-> x*(hmtp_W.0*X.0*toJP.0)
        >;
        TOP2 := map< W_K -> W_K | 
            x :-> x*(hmtp_W.0*X.0*toJP.0*dat[2].0)^-1 
        >;
        Append(~gens_W, TOP1*Gal_vec(W_K, Degree(K) - alpha)*TOP2);
    end for;
    Autotop_gens_K := [
        Homotopism([*gens_V[i], gens_V[i], gens_W[i]*], CohomotopismCategory(3)) : i in [1..#gens_V]
    ]; 
    // assert forall{H : H in Autotop_gens_K | s @ H eq s}; 
    Autotop_gens_p := [Homotopism([*
        Matrix([b @ Ghmtp.2 @ g.2 @@ Ghmtp.2 : b in Basis(V)]),
        Matrix([b @ Ghmtp.1 @ g.1 @@ Ghmtp.1 : b in Basis(V)]), 
        Matrix([b @ Ghmtp.0 @ g.0 @@ Ghmtp.0 : b in Basis(W)])
    *], CohomotopismCategory(3)) : g in Autotop_gens_K];
    // assert forall{H : H in Autotop_gens_p | t_G @ H eq t_G}; 

    G_gens := [x : x in Generators(G)];
    images := [
        ((G_gens @ Gmaps[1]) @ mat_to_map(V, H.2)) @@ Gmaps[1] : H in Autotop_gens_p
    ];
    for i in [1..#G_gens] do 
        for j in [1..Dimension(W)] do 
            im := G_gens;
            im[i] *:= W.j @@ Gmaps[3];
            Append(~images, im);
        end for;
    end for;
    A := AutomorphismGroup(
        G, 
        G_gens, 
        images
    );
    A`Order := #K^18*ord_adj*ord_3*ord_stab;
    A`Group := G;
    return A; 
end intrinsic;
