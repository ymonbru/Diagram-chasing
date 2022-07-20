#Examples of diagram chassing in double complex

from Salamander import *


def fl_inj():#3->7 must be a mono
    g=Void_DC()
    g=add_vertex(g,0,0,"1")
    g=add_vertex(g,0,1,"2")
    g=add_vertex(g,0,2,"3")
    g=add_vertex(g,0,3,"4")
    g=add_vertex(g,1,0,"5")
    g=add_vertex(g,1,1,"6")
    g=add_vertex(g,1,2,"7")
    g=add_vertex(g,1,3,"8")

    g=connect(g)
   
    g=add_exact_hline(g,0,1,2)
    g=add_exact_hline(g,1,1,2)
    g=add_epi(g,0,0,1,0)
    g=add_mono(g,0,1,1,1)
    g=add_mono(g,0,3,1,3)
    return g

def fl_surj():#2->6 must be a mono
    g=Void_DC()
    g=add_vertex(g,0,0,"1")
    g=add_vertex(g,0,1,"2")
    g=add_vertex(g,0,2,"3")
    g=add_vertex(g,0,3,"4")
    g=add_vertex(g,1,0,"5")
    g=add_vertex(g,1,1,"6")
    g=add_vertex(g,1,2,"7")
    g=add_vertex(g,1,3,"8")

    g=connect(g)

    g=add_exact_hline(g,0,1,2)
    g=add_exact_hline(g,1,1,2)

    g=add_epi(g,0,0,1,0)
    g=add_epi(g,0,2,1,2)
    g=add_mono(g,0,3,1,3)

    return g

def fvl_1():# A3->B3 must be an epi
    g=Void_DC()
    g=add_vertex(g,0,0,"A1")
    g=add_vertex(g,0,1,"A2")
    g=add_vertex(g,0,2,"A3")
    g=add_vertex(g,0,3,"A4")
    g=add_vertex(g,0,4,"A5")
    g=add_vertex(g,1,0,"B1")
    g=add_vertex(g,1,1,"B2")
    g=add_vertex(g,1,2,"B3")
    g=add_vertex(g,1,3,"B4")
    g=add_vertex(g,1,4,"B5")

    g=connect(g)

    g=add_exact_hline(g,0,1,3)
    g=add_exact_hline(g,1,1,3)

    g=add_mono(g,0,4,1,4)
    g=add_epi(g,0,1,1,1)
    g=add_epi(g,0,3,1,3)

    return g

def fvl_2():#A3->B3 is a mono
    g=Void_DC()
    g=add_vertex(g,0,0,"A1")
    g=add_vertex(g,0,1,"A2")
    g=add_vertex(g,0,2,"A3")
    g=add_vertex(g,0,3,"A4")
    g=add_vertex(g,0,4,"A5")
    g=add_vertex(g,1,0,"B1")
    g=add_vertex(g,1,1,"B2")
    g=add_vertex(g,1,2,"B3")
    g=add_vertex(g,1,3,"B4")
    g=add_vertex(g,1,4,"B5")

    g=connect(g)

    g=add_exact_hline(g,0,1,3)
    g=add_exact_hline(g,1,1,3)

    g=add_mono(g,0,1,1,1)
    g=add_mono(g,0,3,1,3)
    g=add_epi(g,0,0,1,0)

    return g

def sfl():#then 2->5 is an iso
    g=Void_DC()
    g=add_vertex(g,0,0,"1")
    g=add_vertex(g,0,1,"2")
    g=add_vertex(g,0,2,"3")
    g=add_vertex(g,1,0,"4")
    g=add_vertex(g,1,1,"5")
    g=add_vertex(g,1,2,"6")

    g=connect(g)

    g=add_exact_hline(g,0,0,2)
    g=add_exact_hline(g,1,0,2)


    g=add_mono(g,0,0,0,1)
    g=add_epi(g,0,1,0,2)
    g=add_mono(g,1,0,1,1)
    g=add_epi(g,1,1,1,2)

    g=add_epi(g,0,0,1,0)
    g=add_mono(g,0,0,1,0)
    g=add_epi(g,0,2,1,2)
    g=add_mono(g,0,2,1,2)

    return g

def ntn(n):# n times n
    #then the first line is exact 
    g=Void_DC()
    k=1
    for i in range(n):
        for j in range(n):
            g=add_vertex(g,i,j,str(k))
            k=k+1

    g=connect(g)

    for i in range(1,n):
        g=add_mono(g,i,0,i,1)
        g=add_exact_hline(g,i,1,n-2)
    
    for j in range(n):
        g=add_mono(g,0,j,1,j)
        g=add_exact_vline(g,1,n-2,j)

    return g

def lem263_1():#page 56 of P.Freyd book, B2->B3 is a mono
    g=Void_DC()
    g=add_vertex(g,0,-1,"ZERO",is_zero=True)
    g=add_vertex(g,1,-1,"ZERO",is_zero=True)
    g=add_vertex(g,0,0,"B0")
    g=add_vertex(g,1,0,"B0'")
    g=add_vertex(g,0,1,"B1")
    g=add_vertex(g,1,1,"B1'")
    g=add_vertex(g,0,2,"B2")
    g=add_vertex(g,0,3,"ZERO",is_zero=True)
    g=add_vertex(g,1,2,"B3")
    g=add_vertex(g,-1,2,"ZERO",is_zero=True)

    g=connect(g)

    g=add_iso(g,0,0,1,0)
    g=add_iso(g,0,1,1,1)

    g=add_exact_hline(g,0,0,2)
    g=add_exact_hline(g,1,0,1)
    
    return g

def lem263_2():#page 56 of P.Freyd book, 0->B0'->B1'->B3 is exact 
    g=Void_DC()
    g=add_vertex(g,0,-1,"ZERO",is_zero=True)
    g=add_vertex(g,1,-1,"ZERO",is_zero=True)
    g=add_vertex(g,0,0,"B0")
    g=add_vertex(g,1,0,"B0'")
    g=add_vertex(g,0,1,"B1")
    g=add_vertex(g,1,1,"B1'")
    g=add_vertex(g,0,2,"B2")
    g=add_vertex(g,0,3,"ZERO",is_zero=True)
    g=add_vertex(g,1,2,"B3")
    g=add_vertex(g,-1,2,"ZERO",is_zero=True)

    g=connect(g)

    g=add_iso(g,0,0,1,0)
    g=add_iso(g,0,1,1,1)
    g=add_mono(g,0,2,1,2)

    g=add_exact_hline(g,0,0,2)
    return g

def lem264():#page 57 of P.FReyd book
    g=Void_DC()
    g=add_vertex(g,-1,0,"ZERO",is_zero=True)
    g=add_vertex(g,-1,1,"ZERO",is_zero=True)
    g=add_vertex(g,-1,2,"ZERO",is_zero=True)
    g=add_vertex(g,0,-1,"ZERO",is_zero=True)
    g=add_vertex(g,1,-1,"ZERO",is_zero=True)
    g=add_vertex(g,2,-1,"ZERO",is_zero=True)
    g=add_vertex(g,0,0,"B11")
    g=add_vertex(g,0,1,"B12")
    g=add_vertex(g,0,2,"B13")
    g=add_vertex(g,1,0,"B21")
    g=add_vertex(g,1,1,"B22")
    g=add_vertex(g,1,2,"B23")
    g=add_vertex(g,2,0,"B31")
    g=add_vertex(g,2,1,"B32")
    g=add_vertex(g,3,0,"ZERO",is_zero=True)

    g=connect(g)

    g=add_exact_hline(g,1,0,1)
    g=add_exact_vline(g,0,2,0)
    g=add_exact_vline(g,0,1,1)
    g=add_exact_verti(g,0,2)

    #then 
    g=add_exact_hline(g,0,0,1)
    #if and only if 
    #g=add_exact_horiz(g,2,0)
    return g

def snake():
    g=Void_DC()
    g=add_vertex(g,0,0,"X1")
    g=add_vertex(g,0,1,"X2")
    g=add_vertex(g,0,2,"X3")
    g=add_vertex(g,1,0,"Y1")
    g=add_vertex(g,1,1,"Y2")
    g=add_vertex(g,1,2,"Y3")

    g=connect(g)

    g=add_mono(g,1,0,1,1)
    g=add_epi(g,0,1,0,2)

    g=add_exact_horiz(g,0,1)
    g=add_exact_horiz(g,1,1)

    return g