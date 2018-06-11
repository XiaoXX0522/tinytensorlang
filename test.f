/* Examples for testing */

 lambda x:<a:Bool,b:Bool>. x;
 
"hello";

unit;

lambda x:A. x;

let x=true in x;

timesfloat 2.0 3.14159;

{x=true, y=false}; 
{x=true, y=false}.x;
{true, false}; 
{true, false}.1; 


lambda x:Bool. x;
(lambda x:Bool->Bool. if x false then true else false) 
  (lambda x:Bool. if x then false else true); 

lambda x:Nat. succ x;
(lambda x:Nat. succ (succ x)) (succ 0); 

T = Nat->Nat;
lambda f:T. lambda x:Nat. f (f x);

[1.0,1.0,1.0];
[[1.0,1.0,1.0],[1.0,1.0,1.0],[1.0,1.0,1.0]];
[[[1.0,1.0,1.0],[1.0,1.0,1.0]],[[1.0,1.0,1.0],[1.0,1.0,1.0]]];
[[[[1.0,1.0],[1.0,1.0]],[[1.0,1.0],[1.0,1.0]]],[[[1.0,1.0],[1.0,1.0]],[[1.0,1.0],[1.0,1.0]]]];

nn = [[1.0,2.0,3.0,4.0,5.0,6.0,7.0,8.0,9.0],
      [1.0,2.0,3.0,4.0,5.0,6.0,7.0,8.0,9.0],
      [1.0,2.0,3.0,4.0,5.0,6.0,7.0,8.0,9.0],
      [1.0,2.0,3.0,4.0,5.0,6.0,7.0,8.0,9.0],
      [1.0,2.0,3.0,4.0,5.0,6.0,7.0,8.0,9.0],
      [1.0,2.0,3.0,4.0,5.0,6.0,7.0,8.0,9.0],
      [1.0,2.0,3.0,4.0,5.0,6.0,7.0,8.0,9.0],
      [1.0,2.0,3.0,4.0,5.0,6.0,7.0,8.0,9.0],
      [1.0,2.0,3.0,4.0,5.0,6.0,7.0,8.0,9.0]];
vec = [1.0,2.0,3.0,4.0,5.0,6.0,7.0,8.0,9.0];
1.0 + 1.0;
nn + nn;
nn + 1.0;
1.0 + nn;

product vec vec;
directsum vec vec;
directsum nn nn;
append nn nn;
contract 1 2 nn;
contract 1 2 (product nn vec);
trans 1 2 nn;