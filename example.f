"vector";
vec = [1.0,2.0,3.0];
vec;
"matrix";
mat = [[1.0,2.0,3.0],[4.0,5.0,6.0]];
mat;
"rank3 tensor";
ts3 = [[[1.0,2.0],
        [3.0,4.0]],
       [[5.0,6.0],
        [7.0,8.0]]];
ts3;
"rank4 tensor";
ts4 = [[[[1.0,2.0],
        [3.0,4.0]],
       [[5.0,6.0],
        [7.0,8.0]]],
        [[[1.0,2.0],
        [3.0,4.0]],
       [[5.0,6.0],
        [7.0,8.0]]]];
ts4;

"elementwise arith";
vec + 1.0;
vec * vec;
mat - mat;
mat / 5.0;

"matrix multiply";
mat @ vec;
/* this shall fail: vec @ mat */
"tensor product";
product vec vec;
"contraction";
contract 1 2 (product vec vec);
/* this equals to vec @ vec */

"direct sum";
directsum vec vec;
directsum mat mat;
(directsum mat mat) @ (directsum vec vec);
"append";
append mat mat;

"transpose";
trans 1 2 mat;
"reshape";
reshape [3,2] mat;

"function";
reg = lambda w:Tensor [2,3]. lambda b:Tensor [2].
        lambda x:Tensor [3].
        (w @ x) + b;
reg mat [0.0,0.0] vec;