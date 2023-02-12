# Constructors

We provide two constructors to build $E$-groups in Magma, and we provide a function to determine if some group is an $E$-group. 

Within this package, an $E$-group has a slightly more restrictive definition than in [Maglione&ndash;Stanojkovski](https://arxiv.org/abs/2212.03941). A group $G$ is an $E$-group if there exists a finite field $F$ of characteristic $p\geq 5$, an elliptic curve $E$ over $F$, and $P\in E(F)$ such that $G\cong \mathrm{G}_{E, P}(F)$; see [(Section 1.5) Maglione&ndash;Stanojkovski](https://arxiv.org/abs/2212.03941).


## IsEgroup

**Input**:

- `GrpPC` $G$.


**Output**:

- `BoolElt`. 


Decide if $G$ is an $E$-group or not. This is not constructive in that it will not return $E$, $P$, and $F$ if they exist. If `true` is returned, then the algorithms for isomorphism testing and constructing automorphisms can be applied to $G$. 

#### Example (Is E-group)

We construct groups inspired by du Sautoy's group in [du Sautoy](https://doi.org/10.1007/BF02784157). Let $(x,y) = x^{-1}y^{-1}xy$ be the commutator, and define
\[
    G = \left\langle x_1, \dots, x_6, y_1, y_2, y_3 ~\middle|~ (x_1,x_5)=(x_2,x_4)=(x_3,x_6)=y_1, (x_1,x_6)=(x_3,x_4)=y_2, (x_1,x_4)=(x_2,x_5)=y_3 \right\rangle ,
\]

where all other commutators are defined to be $1$. We construct $G$ in Magma in the following way: 

```C 
> F<x1,x2,x3,x4,x5,x6,y1,y2,y3> := FreeGroup(9);
> G := quo<F | 
    (x1, x2), (x1, x3), (x1, x4)*y3^-1, (x1, x5)*y1^-1, (x1, x6)*y2^-1,
    (x2, x3), (x2, x4)*y1^-1, (x2, x5)*y3^-1, (x2, x6), 
    (x3, x4)*y2^-1, (x3, x5), (x3, x6)*y1^-1,
    (x4, x5), (x4, x6), (x5, x6),
    (y1, x1), (y1, x2), (y1, x3), (y1, x4), (y1, x5), (y1, x6), 
    (y2, x1), (y2, x2), (y2, x3), (y2, x4), (y2, x5), (y2, x6), 
    (y3, x1), (y3, x2), (y3, x3), (y3, x4), (y3, x5), (y3, x6)
    >;
```

Clearly `IsEgroup(G)` would return `false` for many reasons. We define finite $p$-groups for $p=3$ and $p=5$. The $3$-group is not an $E$-group (in our context), but the $5$-group is an $E$-group. 

```C
> P3 := PCGroup(quo<G | x1^3, x2^3, x3^3, x4^3, x5^3, x6^3, 
    y1^3, y2^3, y3^3>
    );
> print P3;
GrpPC : P3 of order 19683 = 3^9
PC-Relations:
    P3.4^P3.1 = P3.4 * P3.9,
    P3.4^P3.3 = P3.4 * P3.8,
    P3.5^P3.2 = P3.5 * P3.7,
    P3.5^P3.3 = P3.5 * P3.9,
    P3.6^P3.1 = P3.6 * P3.8,
    P3.6^P3.2 = P3.6 * P3.9,
    P3.6^P3.3 = P3.6 * P3.7
> IsEgroup(P3);
Prime must be different from 2 and 3.
false
```

```C
> P5 := PCGroup(quo<G | x1^5, x2^5, x3^5, x4^5, x5^5, x6^5, 
    y1^5, y2^5, y3^5>
    );
> print P5;
GrpPC : P5 of order 1953125 = 5^9
PC-Relations:
    P5.4^P5.1 = P5.4 * P5.9,
    P5.4^P5.3 = P5.4 * P5.8,
    P5.5^P5.2 = P5.5 * P5.7,
    P5.5^P5.3 = P5.5 * P5.9,
    P5.6^P5.1 = P5.6 * P5.8,
    P5.6^P5.2 = P5.6 * P5.9,
    P5.6^P5.3 = P5.6 * P5.7
> IsEgroup(P5);
true
```

## Egroup

**Input**:

- `CrvEll` $E$,
- `Pt` $P$,
- optional parameter `twist` default `true`.


**Output**:

- `GrpPC`. 

Returns a finite $p$-group $G$ isomorphic to $G_{E, P}(F)$, where $F$ is the field of definition for $E$. If `twist` is set to `false`, then $\mathrm{G}_{E, P}(F)$ is returned. The underlying field for $E$ must not have characteristic $2$ or $3$, and $P\in E(F)$. 





## RandomEgroup

**Input**:

- `FldFin` $F$,
- optional parameter `twist` default `true`.


**Output**:

- `GrpPC`. 

Returns a "random" $p$-group $G$ isomorphic to $G_{E, P}(F)$, for some $E$ and $P\in E(F)$. If `twist` is set to `false`, then $\mathrm{G}_{E, P}(F)$ is returned. The field $F$ must not have characteristic $2$ or $3$. 

We describe how such a group is constructed at random. Uniformly at random, we select $a,b\in F^2$ such that 
\[ 
    Y^2Z = X^3 + aXZ^2 + bZ^3
\]
defines a smooth cubic in $\mathbb{P}_F^2$. If $\\# E(F) < 10^5$, then we choose $P\in E(F)\setminus \\{\mathcal{O}\\}$ uniformly at random; otherwise we repeatedly select uniformly at random $x_0\in F$ and until we find points in $E(F)$ with $X=x_0$. 

