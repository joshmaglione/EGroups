//
//   Copyright 2022 Joshua Maglione
//
//   Distributed under MIT License
//

import "iso.m" : __Extract_tensor;

// Returns the sequence of three matrices M_P from Ishitsuka's Example 7.6 from
// A positive proportion ... This requires that E be an elliptic curve and P a
// rational point (Magma's special data type).
__Ishitsuka_elliptic_rep := function(E, P)
    assert P[3] ne 0;
    assert Type(P) eq PtEll; 
    K := BaseRing(E);
    a := aInvariants(E)[4];
    lambda := P[1];
    mu := P[2];
    J_P := [
        Matrix(K, 3, 3, [
            1, 0, 0, 
            0, lambda, 1, 
            0, 1, 0
        ]), Matrix(K, 3, 3, [
            0, 1, 0, 
            1, 0, 0,
            0, 0, 0
        ]), Matrix(K, 3, 3, [
            -lambda, -mu, 0, 
            mu, a + lambda^2, 0, 
            0, 0, -1
        ])
    ];
    return J_P;
end function;

// Returns Ishitsuka's representation of a suitable elliptic curve and rational
// point pair (E, P) as an alternating K-bilinear map from K^6 x K^6 into K^3.
__Ishitsuka_elliptic_alt_map := function(E, P, K : twist := true)
    M_P := __Ishitsuka_elliptic_rep(E, P);
    mats := [ChangeRing(M_P[i], K) : i in [1..3]];
    Z := [ZeroMatrix(K, 6, 6) : i in [1..3]];
    Forms := [InsertBlock(Z[i], mats[i], 1, 4) : i in [1..3]];
    Forms := [X - Transpose(X) : X in Forms]; 
    ten_cat := TensorCategory([1,1,1], {{2, 1}, {0}});
    t := Tensor(Forms, 2, 1, ten_cat); 
    assert IsAlternating(t);
    if twist then 
        X := Random(GL(6, K));
        Z := Random(GL(3, K)); 
        H := Homotopism([*X, X, Z*], TensorCategory([1,1,-1], {{2, 1}, {0}}));
        t := t @ H; 
    end if;
    return t;
end function;


// =============================================================================

intrinsic RandomEgroup(K::FldFin : twist := true) -> GrpPC 
{Given a finite field K with characteristic different from 2 and 3, return an E-group over K. A random elliptic curve and point are chosen.} 
    require not Characteristic(K) in {2, 3} : "Characteristic must be different from 2 and 3.";

    repeat 
        S := [Random(K), Random(K)];
    until 4*S[1]^3 + 27*S[2]^2 ne K!0; 
    E := EllipticCurve(S);
    if #K lt 10^5 then 
        Pts := Points(E);
        repeat 
            P := Random(Pts);
        until P[3] eq 1;
    else 
        repeat 
            repeat
                Pts := Points(E, Random(K));
            until #Pts gt 0;
        until exists(P){x : x in Pts | x[3] eq 1}; 
    end if;
    t := __Ishitsuka_elliptic_alt_map(E, P, K : twist := twist); 
    H := HeisenbergGroupPC(t);
    return H; 
end intrinsic;

intrinsic Egroup(E::CrvEll, P::Pt : twist := false) -> GrpPC 
{Given an elliptic curve E over a finite field K, and a point P on E(K), return the E-group associated with these data.}
    K := BaseRing(E);
    require Type(K) eq FldFin : "Base field must be finite."; 
    require not Characteristic(K) in {2, 3} : "Characteristic must be different from 2 and 3.";
    require P in E : "Point must be on given elliptic curve."; 

    t := __Ishitsuka_elliptic_alt_map(E, P, BaseRing(E) : twist := twist); 
    H := HeisenbergGroupPC(t);
    return H; 
end intrinsic;

intrinsic IsEgroup( G::GrpPC ) -> BoolElt
{Decides if G is an E-group.}
    t_G, M := __Extract_tensor(G);
    if Type(t_G) eq BoolElt then 
        print M;
        return false;
    end if;
    A := AdjointAlgebra(t_G);
    type := SimpleParameters(A)[1][1];
    if not type in {"symplectic", "exchange"} then 
        print "Not of decomposable type.";
    end if;
    return true; 
end intrinsic;