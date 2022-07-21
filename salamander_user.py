'''
It's a bridge between the file Salamnder and Diagram_chase

The labeling of the vertex is assumed to be injective'''

import Salamander as sl

g=sl.Void_DC()
facts=[]

def start():
    global g
    g=sl.Void_DC()

def connect():
    global g
    g=sl.connect(g)

def add_vertex(i,j,lab,is_zero=False):
    global g
    g=sl.add_vertex(g,i,j,lab,is_zero=is_zero)

def add_mono(dep,end):
    global g
    (b1,(i,j))=sl.get_is_named(g,dep)
    (b2,(k,l))=sl.get_is_named(g,end)
    if b1 and b2:
        g=sl.add_mono(g,i,j,k,l)
    else:
        if not(b1):
            print("NOT FOUND ",dep)
        if not(b2):
            print("NOT FOUND ",end)

def add_epi(dep,end):
    global g
    (b1,(i,j))=sl.get_is_named(g,dep)
    (b2,(k,l))=sl.get_is_named(g,end)

    if b1 and b2:
        g=sl.add_epi(g,i,j,k,l)
    else:
        if not(b1):
            print("NOT FOUND ",dep)
        if not(b2):
            print("NOT FOUND ",end)

def add_iso(dep,end):
    global g
    (b1,(i,j))=sl.get_is_named(g,dep)
    (b2,(k,l))=sl.get_is_named(g,end)
   
    if b1 and b2:
        g=sl.add_iso(g,i,j,k,l)
    else:
        if not(b1):
            print("NOT FOUND ",dep)
        if not(b2):
            print("NOT FOUND ",end)

def add_exact_horiz(vertex):
    global g
    (b,(i,j))=sl.get_is_named(g,vertex)
    if b:
        g=sl.add_exact_horiz(g,i,j)
    else:
        print("NOT FOUND ", vertex)


def add_exact_vertic(vertex):
    global g
    (b,(i,j))=sl.get_is_named(g,vertex)
    if b:
        g=sl.add_exact_vertic(g,i,j)
    else:
        print("NOT FOUND ", vertex)

def add_exact_hline(dep,end):
    global g
    (b1,(i,j))=sl.get_is_named(g,dep)
    (b2,(k,l))=sl.get_is_named(g,end)
    if b1 and b2:
        if i==k:
            g=sl.add_exact_hline(g,i,j,l)
        else:
            print("NOT ON THE SAME LINE")
    else:
        if not(b1):
            print("NOT FOUND ",dep)
        if not(b2):
            print("NOT FOUND ",end)

def add_exact_vline(dep,end):
    global g
    (b1,(i,j))=sl.get_is_named(g,dep)
    (b2,(k,l))=sl.get_is_named(g,end)
    if b1 and b2:
        if j==l:
            g=sl.add_exact_vline(g,i,k,j)
        else:
            print("NOT ON THE SAME COLUMN")
    else:
        if not(b1):
            print("NOT FOUND ",dep)
        if not(b2):
            print("NOT FOUND ",end)

def translation(statement):
    global g
    n=len(statement)
    if n==2:#('is_zero_obj',name)
        (prop,x)=statement
        (b,(i,j))=sl.get_is_named(g,x)
        if b:
            return (prop,i,j)
        else:
            print("NOT FOUND ",x)
    if n==3:#('is_mono',start,end) or ('is_epi',start,end) or ('is_iso',start,end) or ('is_zero',start,end)
        (prop,x,y)=statement
        (b1,(i,j))=sl.get_is_named(g,x)
        (b2,(k,l))=sl.get_is_named(g,y)
        if b1 and b2:
            return (prop,i,j,k,l)
        else:
            if not(b1):
                print("NOT FOUND ",x)
            if not(b2):
                print("NOT FOUND ",y)
    if n==4:#('is_exact',start,mid,end)
        (prop,x,y,z)=statement
        (b1,(i,j))=sl.get_is_named(g,x)
        (b2,(k,l))=sl.get_is_named(g,y)
        (b3,(m,n))=sl.get_is_named(g,z)
        if b1 and b2 and b3:
            return (prop,i,j,k,l,m,n)
        else:
            if not(b1):
                print("NOT FOUND ",x)
            if not(b2):
                print("NOT FOUND ",y)
            if not(b3):
                print("NOT FOUND ",z)
    if n==5:#('is_exact(connected)',A,B,C,D)
        (prop,x,y,z,w)=statement
        (b1,(i,j))=sl.get_is_named(g,x)
        (b2,(k,l))=sl.get_is_named(g,y)
        (b3,(m,n))=sl.get_is_named(g,z)
        (b4,(o,p))=sl.get_is_named(g,w)
        if b1 and b2 and b3:
            return (prop,i,j,k,l,m,n,o,p)
        else:
            if not(b1):
                print("NOT FOUND ",x)
            if not(b2):
                print("NOT FOUND ",y)
            if not(b3):
                print("NOT FOUND ",z)
            if not(b4):
                print("NOT FOUND ",z)

def display_proof(statement):
    global g
    s=translation(statement)
    sl.aff_proof(g,s)

def display_new_facts():
    global g
    global facts
    facts=sl.new_facts(g)

def display_proof_fact(n):
    global g
    global facts
    sl.aff_proof(g,facts[n])