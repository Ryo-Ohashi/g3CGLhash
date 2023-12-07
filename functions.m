// For a given sequence, return the set of indices which give zero entries.
function collect_zero(seq)
    set := {@ @};
    for j in [1..#seq] do if seq[j] eq 0 then set := set join {j}; end if; end for;
    return set;
end function;

// For given 2-torsions P,Q and R = P+Q of an elliptic curve, return the theta null-point such that P,Q -> 1/2,tau/2.
function torsion_to_nullpoint(P,Q,R)
    a1 := P[1]; a2 := Q[1]; a3 := R[1];
    s1 := (a1-a3)*(a2-a3); s2 := (a3-a2)*(a1-a2); s3 := (a2-a1)*(a3-a1);
    r1 := Sqrt(-s2*s3); r2 := Sqrt(s3*s1); r3 := Sqrt(s1*s2);
    return [r1,r2,r3];
end function;

// For given theta null-points null_j on tau_j, return the theta null-point on Omega = diag(tau_1,tau_2,tau_3).
function product_of_nullpoints(null1,null2,null3)
    prod_null := [K!0: j in [1..64]];
    for j1,j2,j3 in [1..3] do
        index := 0;
        if j1 eq 2 then index +:= 1; elif j1 eq 3 then index +:=  8; end if;
        if j2 eq 2 then index +:= 2; elif j2 eq 3 then index +:= 16; end if;
        if j3 eq 2 then index +:= 4; elif j3 eq 3 then index +:= 32; end if;
        prod_null[index+1] := null1[j1]*null2[j2]*null3[j3];
    end for;
    return prod_null;
end function;

// For given lists corresonding to a symplectic matrix M and a theta null-point, return the theta null-point transformed by M.
function transform_nullpoint(null,index_list,signs_list)
    trans_null := [K!0: j in [1..64]];
    for num in [0,1,2,3,4,5,6,7,8,10,12,14,16,17,20,21,24,27,28,31,32,33,34,35,40,42,45,47,48,49,54,55,56,59,61,62] do
        index := index_list[num+1]; sign := signs_list[num+1];
        if sign eq 0 then
            trans_null[index+1] :=    null[num+1];
        elif sign eq 1 then
            trans_null[index+1] :=  i*null[num+1];
        elif sign eq 2 then
            trans_null[index+1] :=   -null[num+1];
        else
            trans_null[index+1] := -i*null[num+1];
        end if;
    end for;
    return trans_null;
end function;

// For a given theta null-point on Omega/2, return the theta null-point on Omega.
function compute_twoisogeny(full_null)
    non_zero := {@ 1,2,3,4,5,6,7,8 @} sdiff collect_zero([full_null[j]: j in [1..8]]);
    if #non_zero eq 8 then
        sqrt_null := [full_null[1]];
        for k in [2..7] do sqrt_null := Append(sqrt_null,Sqrt(full_null[1]*full_null[k])); end for;
        prod := &*[sqrt_null[k]: k in [2..7]];
        check := full_null[1]*full_null[2]*full_null[3]*full_null[4] + full_null[5]*full_null[6]*full_null[7]*full_null[8] - full_null[33]*full_null[34]*full_null[35]*full_null[36];
        sqrt_null := [2*prod*sqrt_null[k]: k in [1..7]]; sqrt_null[8] := full_null[1]^3*check;
    else
        base := non_zero[1]; sqrt_null := [K!0: j in [1..8]];
        for k in non_zero do
            if k eq base then sqrt_null[k] := full_null[base]; else sqrt_null[k] := Sqrt(full_null[k]*full_null[base]); end if;
        end for;
    end if;
    image_null := [K!0: j in [1..64]];
    product_matrix := Matrix(8,8,[<j,k,sqrt_null[j]*sqrt_null[k]>: j in [1..k], k in [1..8]]);
    for num in [0,1,2,3,4,5,6,7,8,10,12,14,16,17,20,21,24,27,28,31,32,33,34,35,40,42,45,47,48,49,54,55,56,59,61,62] do
        value := 0;
        for k in [1..8] do
            index := isogy_table[1][k][num+1]+1; min := Min(index,k); max := Max(index,k);
            if isogy_table[2][k][num+1] eq 0 then
                value +:= product_matrix[min][max];
            else
                value -:= product_matrix[min][max];
            end if;
        end for;
        image_null[num+1] := value;
    end for;
    return image_null;
end function;

// For a given theta null-point, return the Dixmier-Ohno invariants of the corresponding plane quartic.
function restore_quartic(null)
    assert #collect_zero(null) eq 28;
    s11 := (null[13]*null[6])/(null[34]*null[41]);  s21 := (null[28]*null[6])/(null[55]*null[41]);  s31 := (null[13]*null[28])/(null[34]*null[55]);
    s12 := (null[22]*null[29])/(null[57]*null[50]); s22 := (null[3]*null[29])/(null[48]*null[50]);  s32 := (null[3]*null[22])/(null[48]*null[57]);
    s13 := (null[8]*null[15])/(null[43]*null[36]);  s23 := (null[17]*null[15])/(null[62]*null[36]); s33 := (null[17]*null[8])/(null[62]*null[43]);
    a11 := Sqrt(s11); a21 := Sqrt(s21); a31 := Sqrt(s31);
    a12 := (null[6]*null[22]*null[41]*null[57] + null[13]*null[29]*null[34]*null[50] - null[1]*null[17]*null[46]*null[62])/(2*a11*null[34]*null[41]*null[50]*null[57]);
    a22 := (null[6]*null[29]*null[41]*null[50] + null[3]*null[28]*null[48]*null[55] - null[13]*null[22]*null[34]*null[57])/(2*a21*null[41]*null[48]*null[50]*null[55]);
    a32 := (null[4]*null[21]*null[33]*null[56] - null[3]*null[22]*null[34]*null[55] - null[13]*null[28]*null[48]*null[57])/-(2*a31*null[34]*null[48]*null[55]*null[57]);
    a13 := (a11*null[34]*null[41] - a12*null[50]*null[57])/(null[36]*null[43]);
    a23 := (a22*null[48]*null[50] - a21*null[41]*null[55])/(null[36]*null[62]);
    a33 := (a32*null[48]*null[57] + a31*null[34]*null[55])/(null[43]*null[62]);
    row_vec := Matrix(3,1,[[K!-1],[K!-1],[K!-1]]);
    A := Matrix(3,3,[[1/a11,1/a21,1/a31],[1/a12,1/a22,1/a32],[1/a13,1/a23,1/a33]]);
    l1,l2,l3 := Explode(ElementToSequence(A^(-1)*row_vec));
    B := Matrix(3,3,[[l1*a11,l2*a21,l3*a31],[l1*a12,l2*a22,l3*a32],[l1*a13,l2*a23,l3*a33]]);
    k1,k2,k3 := Explode(ElementToSequence(B^(-1)*row_vec));
    V := Matrix(3,3,[[k1*a11,k2*a21,k3*a31],[k1*a12,k2*a22,k3*a32],[k1*a13,k2*a23,k3*a33]])*A^(-1);
    P2<X,Y,Z> := ProjectiveSpace(K,2);
    xi := [V[1][k]*X + V[2][k]*Y + V[3][k]*Z: k in [1,2,3]];
    C := Curve(P2,(xi[1]*X + xi[2]*Y - xi[3]*Z)^2 - 4*xi[1]*xi[2]*X*Y);
    inv := DixmierOhnoInvariants(C: normalize:=true);
    return inv;
end function;