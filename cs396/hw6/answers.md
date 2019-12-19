# Homework 6 The Network Layer
### Alice McKean
## Problem 1
+ 117.67.91.0/24 = 117.67.91.0 - 117.67.91.255
+ 9.128.0.0/12 = 9.128.0.0 - 9.143.255.255
+ 231.7.23.208/27 = 231.7.23.192 - 231.7.23.223
## Problem 2
In this solution I assume that
If two table entries match with the same size mask then you pick the first table entry (lower index)
### Part A
Start -> A -> B -> D -> End
### Part B
Start -> H -> F -> E -> D -> B -> A -> End
## Problem 3
Milky Way ->
+ Andromeda (1)
+ Triangulum (4)
+ Barnard's Galaxy (2)
+ Centaurus A (6)
+ Messier 81 (13)
+ Sculptor (5)
+ Maffei 1 (10)
## Problem 4
### Time 0
```
Node A:
  A B C D
A 0 7 3 -
B - - - -
C - - - -
D - - - -
Node B:
  A B C D
A - - - -
B 7 0 9 1
C - - - -
D - - - -
Node C: 
  A B C D
A - - - -
B - - - -
C 3 9 0 2
D - - - -
Node D: 
  A B C D
A - - - -
B - - - -
C - - - -
D - 1 2 0
```
### Time 1
```
Node A:
  A B C D
A 0 7 3 5
B 7 0 9 1
C 3 9 0 2
D - 1 2 0
Node B:
  A B C D
A 0 7 3 -
B 7 0 3 1
C 3 9 0 2
D - 1 2 0
Node C: 
  A B C D
A 0 7 3 -
B 7 0 9 1
C 3 3 0 2
D - 1 2 0
Node D: 
  A B C D
A 0 7 3 -
B 7 0 9 1
C 3 9 0 2
D 5 1 2 0
```
### Time 2
```
Node A:
  A B C D
A 0 6 3 5
B 7 0 3 1
C 3 3 0 2
D 5 1 2 0
Node B:
  A B C D
A 0 7 3 5
B 6 0 3 1
C 3 3 0 2
D 5 1 2 0
Node C: 
  A B C D
A 0 7 3 5
B 7 0 3 1
C 3 3 0 2
D 5 1 2 0
Node D: 
  A B C D
A 0 7 3 5
B 7 0 3 1
C 3 3 0 2
D 5 1 2 0
```
### Time 3
```
Node A:
  A B C D
A 0 6 3 5
B 6 0 3 1
C 3 3 0 2
D 5 1 2 0
Node B:
  A B C D
A 0 6 3 5
B 6 0 3 1
C 3 3 0 2
D 5 1 2 0
Node C:
  A B C D
A 0 6 3 5
B 6 0 3 1
C 3 3 0 2
D 5 1 2 0
Node D:
  A B C D
A 0 6 3 5
B 6 0 3 1
C 3 3 0 2
D 5 1 2 0
```
