<import sys
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
    
                

def binaryExtendedEuclideanAlgorithm_version2(u, v):
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
        if u <= t2:
            t2 = t2 - u

        if u3 > v3:
            t3 = u3 - v3
        else:
            t3 = v3 - u3            

    return (u - u2)
    



def run1(x):
  inv = binaryExtendedEuclideanAlgorithm_version2(P(),x)
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
    test1()
  
if __name__ == '__main__':
    main()

