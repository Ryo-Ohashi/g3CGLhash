load "tables.m";

lambda := 128;
p := Random(2^Ceiling(lambda/2));
repeat p := NextPrime(p); until p mod 4 eq 3;
K<i> := ExtensionField<GF(p),x|x^2+1>;
R<x> := PolynomialRing(K);

load "functions.m";

function g3CGLhash(message)
    E := EllipticCurve(x^3-x); P := E![1,0]; Q := E![-1,0]; R := E![0,0];
    null := torsion_to_nullpoint(P,Q,R);
    first_null := product_of_nullpoints(null,null,null);
    trans_null := transform_nullpoint(first_null,trans_table[1][23],trans_table[2][23]);
    image_null := compute_twoisogeny(trans_null);
    mbase64 := IntegerToSequence(message,64);
    for k := 1 to #mbase64 do
        bin := mbase64[k] + 1;
        trans_null := transform_nullpoint(image_null,trans_table[1][bin],trans_table[2][bin]);
        image_null := compute_twoisogeny(trans_null);
    end for;
    return restore_quartic(image_null);
end function;

message := Random(2^100);
time g3CGLhash(message);