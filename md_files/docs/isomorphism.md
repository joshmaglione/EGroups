# Isomorphism

We provide two functions dealing with isomorphisms of $E$-groups. One for deciding isomorphism between two $E$-groups, and the other for constructing a generating set for the automorphism group of such groups. In order to not overlap with existing Magma functions, functions here have the prefix `EG`.


## EGAutomorphismGroup

**Input**:

- `GrpPC` $G$.


**Output**:

- `GrpAuto` $A$.

Return $A=\mathrm{Aut}(G)$ provided $G$ is an $E$-group. 



## EGIsIsomorphic

**Input**:

- `GrpPC` $G$,
- `GrpPC` $H$.


**Output**:

- `BoolElt`,
- `Map` $\varphi$. 

Decide if $G$ and $H$ are $E$-groups and if $G\cong H$, and if so return an isomorphism $\varphi : G \to H$. 

