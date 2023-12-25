import sys
import os
import json
import argparse
import re

def P() :
    return 21888242871839275222246405745257275088696311157297823662689037894645226208583

def binaryExtendedEuclideanAlgorithm(modulus,base):
    u = base
    v = modulus
    b = 1
    c = 0
    while (u != 1 and v != 1):
        while u & 1 != 1:
            u = u >> 1
            current = b
            if current & 1 == 0:
                b = b >> 1
            else:
                b = (b + modulus) >> 1

        while v % 2 != 1:
            v = v >> 1
            current = c
            if current & 1 == 0:
                c = c >> 1
            else:
                c = (c + modulus) >> 1        
        if v > u:
            v = v - u
            if c < b:
                c = c + modulus
            c = c - b
        else:
            u = u - v
            if b < c:
                b = b + modulus
            b = b - c
    if u == 1:
        return b
    else:
        return c
    
                
        


def simplify_ts(t2,t3,u,v):
    while t3 % 2 == 0:
        if t2 % 2 == 0:
            (t2,t3) = (t2 // 2, t3 // 2)
        else:
            (t2,t3) = ((t2-u)//2, t3 // 2)
    return (t2,t3)


    

def main61(u, v):
    (u2,u3) = (0, u)
    (t2,t3) = (1, v)    

    while t3 & 1 == 0:
        if t2 & 1 == 0:
            (t2,t3) = (t2 >> 1, t3 >> 1)
        else:
            (t2,t3) = ((t2+u) >> 1, t3 >> 1)    
    (v2, v3) = (t2, t3)
    (t2, t3) = (v2, u3-v3)

    while (u3 != v3):
        while t3 & 1 == 0:
            if t2 & 1 == 0:
                (t2,t3) = (t2 >> 1, t3 >> 1)
            else:
                (t2,t3) = ((t2+u) >> 1, t3 >> 1)
        
        if v3 < u3:            
            (u2,u3) = (t2, t3)
        else:            
            (v2, v3) = (t2, t3)
            
        t2 = u2+v2
        if t2 >= u:
            t2 = t2 - u

        if u3 > v3:
            t3 = u3 - v3
        else:
            t3 = v3 - u3            

    return (u - u2)

def main6(u, v):
    (u2,u3) = (0, u)
    (t2,t3) = (-1, v)    

    while t3 % 2 == 0:
        if t2 % 2 == 0:
            (t2,t3) = (t2 // 2, t3 // 2)
        else:
            (t2,t3) = ((t2-u)//2, t3 // 2)    
    (v2, v3) = (-t2, t3)
    (t2, t3) = (u2-v2, abs(u3-v3)) 

    while (t3 != 0):


        while t3 % 2 == 0:
            if t2 % 2 == 0:
                (t2,t3) = (t2 // 2, t3 // 2)
            else:
                (t2,t3) = ((t2-u)//2, t3 // 2)
        if v3 < u3:
            (u2,u3) = (t2,t3)
            (t2, t3) = (u2-v2, abs(u3 - v3))
        else:
            (v2, v3) = (-t2, t3)
            (t2, t3) = (u2-v2, abs(u3 - v3))
    return u2
    

def run1(x):
  inv = main61(P(),x)
  return (x * inv) % P()

def run2(x):
  inv = binaryExtendedEuclideanAlgorithm(P(),x)
  return (x * inv) % P()

def test1():
    c = 1
    while c < 100000:
        r = run1(c)
        assert(r == 1)
        c = c + 1

def test2():
    c = 1
    while c < 100000:
        r = run2(c)
        assert(r == 1)
        c = c + 1

def main():
    test2()
  
if __name__ == '__main__':
    main()


  #   proc main6(u : int, v : int) = {
  #     var u2,u3,v2,v3,t2,t3;
  #     (u2,u3,v3,v2,t2,t3) <- (0,0,0,0,0,0);
  #     (v2,v3) <- ((1-u), v);
  #     (u2,u3) <- (0, u);
  #     (t2,t3) <- (-1, v);

  #     (t2,t3) <@ simplify_ts(t2, t3, u, v);
  #     (v2, v3) <- (-u-t2, t3);

  #     (t2, t3) <- (u2-v2, `|u3-v3|);

  #     while (t3 <> 0){
  #       (t2,t3) <@ simplify_ts(t2, t3, u, v);
  #       if (v3 < u3){
  #         (u2, u3) <- (t2, t3);
  #         (t2, t3) <- (u2-v2, `|u3 - v3|);          
  #       }else{
  #         (v2, v3) <- (-u-t2, t3);
  #         (t2, t3) <- (u2-v2, `|u3 - v3|);          
  #       }
  #      }
  #     return (u2, u3);
  # }
