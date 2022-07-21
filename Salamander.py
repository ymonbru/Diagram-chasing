''' a grid is given by the tuple:
(exact,labl,zero,mono,epi,zobj,shad,don,rec,homh,homv,proof)=g

    *exact is a dictionary of exact conditions
    *labl is the dictionary of the name of the vertex declared
    *zero,mono, epi  knows if a declared map is zero/epi/mono
    *zobj know if a declared object is zero
    *shad (shadow) is the graph built with donnor recptor,.... from the salamander lemma
    *don/rec/homh/hov remember the number of the donor/recptor/ horizontal homology/vertical homology in the shadow graph
    *a last dictionary for proof
    proof[number for facts]=(string of the fact,rule applied,[list of premises])

'''
import graph_for_salamandre as gr

##Fisrt add the vertex then use the connect function and finaly add the exact/epi/monà/zero condition

def exact(g):
    (exact,_,_,_,_,_,_,_,_,_,_,_)=g
    return exact
def lbl(g):
    (_,labl,_,_,_,_,_,_,_,_,_,_)=g
    return labl
def zero_map(g):
    (_,_,zero,_,_,_,_,_,_,_,_,_)=g
    return zero
def mono_map(g):
    (_,_,_,mono,_,_,_,_,_,_,_,_)=g
    return mono
def epi_map(g):
    (_,_,_,_,epi,_,_,_,_,_,_,_)=g
    return epi
def zobj_num(g):
    (_,_,_,_,_,zobj,_,_,_,_,_,_)=g
    return zobj
def shadow_gr(g):
    (_,_,_,_,_,_,shad,_,_,_,_,_)=g
    return shad
def don_num(g):
    (_,_,_,_,_,_,_,don,_,_,_,_)=g
    return don
def rec_num(g):
    (_,_,_,_,_,_,_,_,rec,_,_,_)=g
    return rec
def homh_num(g):
    (_,_,_,_,_,_,_,_,_,homh,_,_)=g
    return homh
def homv_num(g):
    (_,_,_,_,_,_,_,_,_,_,homv,_)=g
    return homv
def proof(g):
    (_,_,_,_,_,_,_,_,_,_,_,pf)=g
    return pf

#######
#the grid is assumed to exist with the maps and son on: by defautl there is a zero object and a zero map in the things non declared
# but kernel and cokernel can be added 

def Void_DC():
    return (dict(),dict(),dict(),dict(),dict(),dict(),gr.graph_void(),dict(),dict(),dict(),dict(),dict())

#do not use the is_zero except for an hypothesis
def add_vertex(g,i,j,lab,is_zero=False):# declared a vertex at (i,j) with name lab
    (exact,labl,zero,mono,epi,zobj,shad,don,rec,homh,homv,pf)=g
    labl[i,j]=lab# it must be a string non void
    zobj[i,j]=False
    new_g=(exact,labl,zero,mono,epi,zobj,shad,don,rec,homh,homv,pf)
    new_g=add_shadow_square(new_g,i,j,lab)
    #it's important to build the shadow square before adding the 0
    if is_zero:
        new_g=add_zero_obj(new_g,i,j)
    return new_g

def add_shadow_square(g,i,j,lab,is_zero=False):#add the square with donnor/receptor and cie
    (exact,labl,zero,mono,epi,zobj,shad,don,rec,homh,homv,pf)=g

    (shad,d)=gr.add_vertex(shad,'donor '+lab)
    (shad,r)=gr.add_vertex(shad,'receptor '+lab)
    (shad,h)=gr.add_vertex(shad,'h_hom '+lab)
    (shad,v)=gr.add_vertex(shad,"v_hom "+lab)

    if is_zero or is_zero_obj(g,i,j):
        pr=[('is_zero_obj',i,j)]
        rl="if an object is 0 then it's donor is 0 "
        shad=gr.add_zero_obj(shad,d,rule=rl,prem=pr)
        rl="if an object is 0 then it's receptor is 0"
        shad=gr.add_zero_obj(shad,r,rule=rl,prem=pr)
        rl="if an object is 0 then it's h_hom is 0"
        shad=gr.add_zero_obj(shad,h,rule=rl,prem=pr)
        rl="if an object is 0 then it's v_hom is 0"
        shad=gr.add_zero_obj(shad,v,rule=rl,prem=pr)
    don[i,j]=d
    rec[i,j]=r
    homh[i,j]=h
    homv[i,j]=v

    shad,_=gr.add_edge(shad,r,h)
    shad,_=gr.add_edge(shad,r,v)
    shad,_=gr.add_edge(shad,r,d)
    shad,_=gr.add_edge(shad,h,d)
    shad,_=gr.add_edge(shad,v,d)

    new_g=(exact,labl,zero,mono,epi,zobj,shad,don,rec,homh,homv,pf)
    return new_g

def connect(g):#apply this function when there is no more vertex to add
    #it will add kernel and cokernel at the edge of the diagram
    new_g,new_exact=add_ker_coker(g)

    labl=lbl(new_g)
    for (i,j) in labl:#the vertex that are declared
        l=[(i,j,i+1,j),(i,j,i,j+1),(i-1,j,i,j),(i,j-1,i,j),(i,j,i+1,j+1),(i-1,j-1,i,j)]
        for (a,b,c,d) in l:
            if not(is_dec_map(g,a,b,c,d)):
                new_g=add_edge(new_g,a,b,c,d)

    for (name,k,l,i,j,m,n) in new_exact:
        di=i-k
        dj=j-l

        if name=='ker':
            if di==1 and dj==0:
                new_g=add_exact_verti(new_g,k,l)
                new_g=add_exact_verti(new_g,i,j)
            elif di==0 and dj==1:
                new_g=add_exact_horiz(new_g,k,l)
                new_g=add_exact_horiz(new_g,i,j)
        if name=='coker':
            if di==1 and dj==0:
                new_g=add_exact_verti(new_g,m,n)
                new_g=add_exact_verti(new_g,i,j)
            elif di==0 and dj==1:
                new_g=add_exact_horiz(new_g,m,n)
                new_g=add_exact_horiz(new_g,i,j)


    return new_g

def add_ker_coker(g):
    #In order to avoid problem it can be used after the function complete
    labl=lbl(g).copy()#because otherwise it's modified during the loop
    new_g=g
    new_exact=[]
    for (i,j) in labl:#the vertex that are declared
        for (k,l,m,n) in [(i-1,j,i+1,j),(i,j-1,i,j+1)]:#if there is no kernel at the edge then add it 
            if not(is_dec(g,k,l)):
                A=labl[i,j]
                B=labl.get((m,n),"ZERO")
                name='K('+A+'->'+B+')'
                new_g=add_vertex(new_g,k,l,name)
                new_exact.append(('ker',k,l,i,j,m,n))# the edge have to be added before the exact conditions
        for (k,l,m,n) in [(i-1,j,i+1,j),(i,j-1,i,j+1)]:#if there is no cokernel at the edge then add it
            if not(is_dec(g,m,n)):
                B=labl[i,j]
                A=labl.get((k,l),"ZERO")
                name='CK('+A+'->'+B+')'
                new_g=add_vertex(new_g,m,n,name)
                new_exact.append(('coker',k,l,i,j,m,n))# the edge have to be added before the exact conditions

    return new_g,new_exact

def add_shadow_edge(g,o,t):
    (exact,labl,zero,mono,epi,zobj,shad,don,rec,homh,homv,pf)=g
    new_g=g
    new_e=gr.get_arrow(shad,o,t)
    if new_e== -1:
        shad,new_e=gr.add_edge(shad,o,t)
        new_g=(exact,labl,zero,mono,epi,zobj,shad,don,rec,homh,homv,pf)
        new_g=propagate_info_shadow(new_g)
    return (new_g,new_e)

def add_edge(g,i,j,k,l):#declared an edge: (i,j)
    (exact,labl,zero,mono,epi,zobj,shad,don,rec,homh,homv,pf)=g
    new_g=g
    zero[i,j,k,l]=False
    new_g=(exact,labl,zero,mono,epi,zobj,shad,don,rec,homh,homv,pf)
    if is_zero_obj(g,i,j):
        r='if X=0 then f:X->Y=0'
        pr=[('is_zero_obj',i,j)]
        new_g=add_zero_map(new_g,i,j,k,l,rule=r,prem=pr)
    if is_zero_obj(g,k,l):
        r='if Y=0 then f:X->Y=0'
        pr=[('is_zero_obj',k,l)]
        new_g=add_zero_map(new_g,i,j,k,l,rule=r,prem=pr)

    ### add the salamnder lemma into shad
    if k==i and l==j+1 and not(is_zero_obj(new_g,i,j) and is_zero_obj(new_g,k,l)):
        (new_g,da)=get_donnor(new_g,i,j)
        (new_g,ra)=get_receptor(new_g,i,j)
        (new_g,ha)=get_hhom(new_g,i,j)
        (new_g,db)=get_donnor(new_g,k,l)
        (new_g,rb)=get_receptor(new_g,k,l)
        (new_g,hb)=get_hhom(new_g,k,l)
        (new_g,dc)=get_donnor(new_g,i-1,j)
        (new_g,rd)=get_receptor(new_g,i+1,j+1)

        (new_g,a)=add_shadow_edge(new_g,dc,ha)
        (new_g,_)=add_shadow_edge(new_g,dc,ra)
        (new_g,_)=add_shadow_edge(new_g,ra,ha)
        (new_g,b)=add_shadow_edge(new_g,ha,da)
        (new_g,c)=add_shadow_edge(new_g,da,rb)
        (new_g,d)=add_shadow_edge(new_g,rb,hb)
        (new_g,e)=add_shadow_edge(new_g,hb,rd)
        (new_g,_)=add_shadow_edge(new_g,hb,db)
        (new_g,_)=add_shadow_edge(new_g,db,rd)

        lab=lbl(new_g)
        domain=lab.get((i,j),"ZERO")
        codomain=lab.get((k,l),"ZERO")
        rl=' by horizontal Salamander lemma at '+domain+'->'+codomain
        new_g=add_shadow_exact(new_g,a,b,rule=rl)
        new_g=add_shadow_exact(new_g,b,c,rule=rl)
        new_g=add_shadow_exact(new_g,c,d,rule=rl)
        new_g=add_shadow_exact(new_g,d,e,rule=rl)

    if k==i+1 and l==j and not(is_zero_obj(new_g,i,j) and is_zero_obj(new_g,k,l)):
        (new_g,da)=get_donnor(new_g,i,j)
        (new_g,ra)=get_receptor(new_g,i,j)
        (new_g,va)=get_vhom(new_g,i,j)
        (new_g,db)=get_donnor(new_g,k,l)
        (new_g,rb)=get_receptor(new_g,k,l)
        (new_g,vb)=get_vhom(new_g,k,l)
        (new_g,dc)=get_donnor(new_g,i,j-1)
        (new_g,rd)=get_receptor(new_g,i+1,j+1)

        (new_g,a)=add_shadow_edge(new_g,dc,va)
        (new_g,_)=add_shadow_edge(new_g,dc,ra)
        (new_g,_)=add_shadow_edge(new_g,ra,va)
        (new_g,b)=add_shadow_edge(new_g,va,da)
        (new_g,c)=add_shadow_edge(new_g,da,rb)
        (new_g,d)=add_shadow_edge(new_g,rb,vb)
        (new_g,e)=add_shadow_edge(new_g,vb,rd)
        (new_g,_)=add_shadow_edge(new_g,vb,db)
        (new_g,_)=add_shadow_edge(new_g,db,rd)

        lab=lbl(new_g)
        domain=lab.get((i,j),"ZERO")
        codomain=lab.get((k,l),"ZERO")
        rl=' by vertical Salamander lemma at '+domain+'->'+codomain
        new_g=add_shadow_exact(new_g,a,b,rule=rl)
        new_g=add_shadow_exact(new_g,b,c,rule=rl)
        new_g=add_shadow_exact(new_g,c,d,rule=rl)
        new_g=add_shadow_exact(new_g,d,e,rule=rl)

    return propagate_info_edge(new_g,i,j,k,l)

def add_zero_obj(g,i,j,rule=' by assumption',prem=[]):# the object at (i,j) (if it is declared because they are 0 by default)
    (exact,labl,zero,mono,epi,zobj,shad,don,rec,homh,homv,pf)=g
    new_g=g
    #labl are non void string!then lab=True
    if is_dec(new_g,i,j) and not(is_zero_obj(new_g,i,j)):
        zobj[i,j]=True
        pf[('is_zero_obj',i,j)]=(rule,prem)
        new_g=(exact,labl,zero,mono,epi,zobj,shad,don,rec,homh,homv,pf)
        
        d=don[i,j]# the donnor exist because the vertex was declared
        r=rec[i,j]
        h=homh[i,j]
        v=homv[i,j]

        pr=[('is_zero_obj',i,j)]
        rl="if an object is 0 then it's donnor is 0"
        new_g=add_shadow_zero_obj(new_g,d,rule=rl,prem=pr)
        rl="if an object is 0 then it's receptor is 0"
        new_g=add_shadow_zero_obj(new_g,r,rule=rl,prem=pr)
        rl="if an object is 0 then it's h_hom is 0"
        new_g=add_shadow_zero_obj(new_g,h,rule=rl,prem=pr)
        rl="if an object if 0 then it's v_hom is 0"
        new_g=add_shadow_zero_obj(new_g,v,rule=rl,prem=pr)
        return propagate_info_vertex(new_g,i,j)
    return new_g

def add_shadow_zero_obj(g,x,rule=' by assumption',prem=[]):
    (exact,labl,zero,mono,epi,zobj,shad,don,rec,homh,homv,pf)=g
    new_g=g
    if not(gr.is_zero(shad,x)):
        shad=gr.add_zero_obj(shad,x,rule=rule,prem=prem)
        new_g=(exact,labl,zero,mono,epi,zobj,shad,don,rec,homh,homv,pf)
        new_g=propagate_info_shadow(new_g)
    return new_g

def add_zero_map(g,i,j,k,l,rule=' by assumption',prem=[]):# the map (i,j)->(k,l) is now declared to be zero (if it is not by default)
    (exact,labl,zero,mono,epi,zobj,shad,don,rec,homh,homv,pf)=g
    new_g=g
    if is_dec_map(g,i,j,k,l) and not(is_zero_map(g,i,j,k,l,)):
        zero[i,j,k,l]=True
        pf[('is_zero',i,j,k,l)]=(rule,prem)
        new_g=(exact,labl,zero,mono,epi,zobj,shad,don,rec,homh,homv,pf)
        return propagate_info_edge(new_g,i,j,k,l)
    return new_g

def add_shadow_zero_map(g,o,t,rule=' by assumption',prem=[]):
    (exact,labl,zero,mono,epi,zobj,shad,don,rec,homh,homv,pf)=g
    new_g=g
    f=gr.get_arrow(shad,o,t)
    if not(gr.is_zero_map(shad,f)):
        shad=gr.add_zero(shad,f,rule=rule,prem=prem)
        new_g=(exact,labl,zero,mono,epi,zobj,shad,don,rec,homh,homv,pf)
        new_g=propagate_info_shadow(new_g)
    return new_g

def add_epi(g,i,j,k,l,rule=' by assumption',prem=[]):# the map (i,j)->(k,l) is now declared to be epi
    (exact,labl,zero,mono,epi,zobj,shad,don,rec,homh,homv,pf)=g
    if is_dec_map(g,i,j,k,l) and not(is_epi(g,i,j,k,l,)):
        epi[i,j,k,l]=True
        pf[('is_epi',i,j,k,l)]=(rule,prem)
        new_g=(exact,labl,zero,mono,epi,zobj,shad,don,rec,homh,homv,pf)
        if mono.get((i,j,k,l),False):
            stat=('is_iso',i,j,k,l)
            rl='if f is a mono and an epi then f is an iso'
            pr=[('is_mono',i,j,k,l),('is_epi', i,j,k,l)]
            new_g=add_proof(new_g,stat,rl,pr)
        return propagate_info_edge(new_g,i,j,k,l)
    return g

def add_mono(g,i,j,k,l,rule=' by assumption',prem=[]):# the map (i,j)->(k,l) is now declared to be mono
    (exact,labl,zero,mono,epi,zobj,shad,don,rec,homh,homv,pf)=g
    if is_dec_map(g,i,j,k,l) and not(is_mono(g,i,j,k,l)):
        mono[i,j,k,l]=True
        pf[('is_mono',i,j,k,l)]=(rule,prem)
        new_g=(exact,labl,zero,mono,epi,zobj,shad,don,rec,homh,homv,pf)
        if epi.get((i,j,k,l),False):
            stat=('is_iso',i,j,k,l)
            rl='if f is a mono and an epi then f is an iso'
            pr=[('is_mono',i,j,k,l),('is_epi', i,j,k,l)]
            new_g=add_proof(new_g,stat,rl,pr)
        return propagate_info_edge(new_g,i,j,k,l)
    return g

def add_iso(g,i,j,k,l,rule=' by assumption',prem=[]):
    new_g=g
    new_g=add_mono(new_g,i,j,k,l,rule=rule,prem=prem)
    new_g=add_epi(new_g,i,j,k,l,rule=rule,prem=prem)
    return new_g

def add_exact(g,i,j,k,l,m,n,rule=' by assumption',prem=[]):#the composition of (i,j)->(k,l) and (k,l)->(m,n) is now exact
    (exact,labl,zero,mono,epi,zobj,shad,don,rec,homh,homv,pf)=g
    if is_dec_map(g,i,j,k,l) and is_dec_map(g,k,l,m,n) and not(is_exact(g,i,j,k,l,m,n)):
        exact[i,j,k,l,m,n]=True
        pf[('is_exact',i,j,k,l,m,n)]=(rule,prem)
        new_g=(exact,labl,zero,mono,epi,zobj,shad,don,rec,homh,homv,pf)

        if k==i+1 and m==i+2 and j==l and j==n:
            new_g,v=get_vhom(new_g,k,l)
            r='if the vertical composition is exact then the v_hom is 0'
            pr=[('is_exact',i,j,k,l,m,n)]
            new_g=add_shadow_zero_obj(new_g,v,rule=r,prem=pr)
        if l==j+1 and n==j+2 and k==i and m==i:
            new_g,h=get_hhom(new_g,k,l)
            r='if the horizontal composition is exact then the h_hom is 0'
            pr=[('is_exact',i,j,k,l,m,n)]
            new_g=add_shadow_zero_obj(new_g,h,rule=r,prem=pr)
        return propagate_info_exact(new_g,i,j,k,l,m,n)
    return g

def add_shadow_exact(g,e,f,rule=' by assumption',prem=[]):
    (exact,labl,zero,mono,epi,zobj,shad,don,rec,homh,homv,pf)=g
    shad=gr.add_exact(shad,e,f,rule=rule,prem=prem)
    new_g=(exact,labl,zero,mono,epi,zobj,shad,don,rec,homh,homv,pf)
    new_g=propagate_info_shadow(new_g)
    return new_g

def add_exact_verti(g,i,j,rule=' by assumption',prem=[]):
    return add_exact(g,i-1,j,i,j,i+1,j,rule=rule,prem=prem)

def add_exact_horiz(g,i,j,rule=' by assumption',prem=[]):
    return add_exact(g,i,j-1,i,j,i,j+1,rule=rule,prem=prem)

#these four function can only be used for add hypothesis
def add_exact_vline(g,i_dep,i_end,j):
    new_g=g
    for i in range(i_dep,i_end+1):
        new_g=add_exact_verti(new_g,i,j)
    return new_g

def add_exact_hline(g,i,j_dep,j_end):
    new_g=g
    for j in range(j_dep,j_end+1):
        new_g=add_exact_horiz(new_g,i,j)
    return new_g

def add_proof(g,statement,rule,prem):
    (exact,labl,zero,mono,epi,zobj,shad,don,rec,homh,homv,pf)=g
    pf[statement]=(rule,prem)
    new_g=(exact,labl,zero,mono,epi,zobj,shad,don,rec,homh,homv,pf)
    return new_g

def add_new_shad(g,n_shad):
    (exact,labl,zero,mono,epi,zobj,shad,don,rec,homh,homv,pf)=g
    new_g=(exact,labl,zero,mono,epi,zobj,n_shad,don,rec,homh,homv,pf)
    return new_g

########
#these function take into account that the grid is infinite and then an object or a map is zero by defaul

def is_zero_obj(g,i,j):
    zobj=zobj_num(g)
    iszo=zobj.get((i,j),True)
    return iszo

def is_zero_map(g,i,j,k,l):
    zero=zero_map(g)
    iszm=zero.get((i,j,k,l),True)
    return iszm

def is_mono(g,i,j,k,l):
    mono=mono_map(g)
    if is_dec_map(g,i,j,k,l):
        return mono.get((i,j,k,l),False)
    else:
        #the map is a zero map
        return is_zero_obj(g,i,j)

def is_epi(g,i,j,k,l):

    epi=epi_map(g)
    if is_dec_map(g,i,j,k,l):
        return epi.get((i,j,k,l),False)
    else:
        #the map is a zero map
        return is_zero_obj(g,k,l)

def is_exact(g,i,j,k,l,m,n):
    ex=exact(g)
    same_dir=(k==i+1 and m==i+2 and l==j and n==j)or(k==i and m==i and l==j+1 and n==j+2)
    if same_dir:
        if is_zero_map(g,i,j,k,l) and is_mono(g,k,l,m,n):
            return True
        if is_epi(g,i,j,k,l) and is_zero_map(g,k,l,m,n):
            return True
        return ex.get((i,j,k,l,m,n),False)
    return False#this case does not happen

def is_dec_exact(g,i,j,k,l,m,n):
    ex=exact(g)
    return ex.get((i,j,k,l,m,n),False)

def is_dec_map(g,i,j,k,l):
    zero=zero_map(g)
    dec=zero.get((i,j,k,l),-1)
    return (dec != -1)

def is_dec(g,i,j):
    lab=lbl(g)
    l=lab.get((i,j),-1)
    return (l != -1)

def get_donnor(g,i,j):#gives the donnor if it exists and add it otherwise
    new_g=g
    don=don_num(g)
    d=don.get((i,j),-1)
    if d== -1:
        new_g=add_shadow_square(new_g,i,j,lab="ZERO",is_zero=True)
        don=don_num(new_g)
        d=don.get((i,j),-1)#it is not -1
    return (new_g,d)

def get_receptor(g,i,j):#gives the receptor if it exists and add it otherwise
    new_g=g
    rec=rec_num(g)
    r=rec.get((i,j),-1)
    if r== -1:
        new_g=add_shadow_square(new_g,i,j,lab="ZERO",is_zero=True)
        rec=rec_num(new_g)
        r=rec.get((i,j),-1)#it is not -1
    return (new_g,r)

def get_hhom(g,i,j):#gives the receptor if it exists and add it otherwise
    new_g=g
    hhom=homh_num(g)
    h=hhom.get((i,j),-1)
    if h== -1:
        new_g=add_shadow_square(new_g,i,j,lab="ZERO",is_zero=True)
        hhom=homh_num(new_g)
        h=hhom.get((i,j),-1)#it is not -1
    return (new_g,h)

def get_vhom(g,i,j):#gives the receptor if it exists and add it otherwise
    new_g=g
    vhom=homv_num(g)
    v=vhom.get((i,j),-1)
    if v== -1:
        new_g=add_shadow_square(new_g,i,j,lab="ZERO",is_zero=True)
        vhom=homv_num(new_g)
        v=vhom.get((i,j),-1)#it is not -1
    return (new_g,v)

def get_is_named(g,name):#return one vertex that has label name, used in salamander_user fils
    lab=lbl(g)
    for (i,j) in lab:
        if lab[i,j]==name:
            return (True,(i,j))
    return (False,(0,0))
    

######### COMPUTE NEW INFO

def propagate_info_vertex(g,i,j):
    new_g=g
    if is_zero_obj(new_g,i,j):
        lo=[(i,j,i+1,j),(i,j,i,j+1)]
        le=[(i-1,j,i,j),(i,j-1,i,j)]
        pr=[('is_zero_obj',i,j)]
        for (a,b,c,d) in lo:
            if not(is_zero_map(new_g,a,b,c,d)):
                r='if X=0 then f:X->Y is a mono'
                new_g=add_zero_map(new_g,a,b,c,d,rule=r,prem=pr)
                new_g=add_mono(new_g,a,b,c,d,rule=r,prem=pr)
        for (a,b,c,d) in le:
            if not(is_zero_map(new_g,a,b,c,d)):
                r='if Y=0 then f:X->Y is an epi'
                new_g=add_zero_map(new_g,a,b,c,d,rule=r,prem=pr)
                new_g=add_epi(new_g,a,b,c,d,rule=r,prem=pr)
    return new_g

def propagate_info_edge(g,i,j,k,l):
    new_g=g
    if is_zero_map(new_g,i,j,k,l):
        pr=[('is_zero',i,j,k,l)]
        d=get_donnor(new_g,i,j)
        r=get_receptor(new_g,k,l)
        rl='if f=0 then f intramural is 0'
        #the safety test is done in add_shadow
        new_g=add_shadow_zero_map(new_g,d,r,rule=rl,prem=pr)
        if is_mono(new_g,i,j,k,l) and not(is_zero_obj(g,i,j)):
            r='if f:X->Y is mono and 0 then X=0'
            pr=[('is_zero',i,j,k,l),('is_mono',i,j,k,l)]
            new_g=add_zero_obj(g,i,j,rule=r,prem=pr)
        if is_epi(g,i,j,k,l) and not(is_zero_obj(g,k,l)):
            r='if f:X->Y is epi and 0 then Y=0'
            pr=[('is_zero',i,j,k,l),('is_epi',i,j,k,l)]
            new_g=add_zero_obj(g,k,l,rule=r,prem=pr)
    if k== i+1 and l==j+1:
        if is_mono(new_g,i,j,k,l):
            new_g,d=get_donnor(new_g,i,j)
            r='if a diagonal map is mono then the donnor of the origin is 0'
            pr=[('is_mono',i,j,k,l)]
            new_g=add_shadow_zero_obj(new_g,d,rule=r,prem=pr) 
            if not(is_mono(new_g,i,j,i,j+1)):
                r='if g°f is mono then f is mono'
                new_g=add_mono(new_g,i,j,i,j+1,rule=r,prem=pr)
            if not(is_mono(new_g,i,j,i+1,j)):
                r='if g°f is mono then f is mono'
                new_g=add_mono(g,i,j,i+1,j,rule=r,prem=pr)
            #the rule g°f=0 g mono => f=0 will be a consequence of of addind those mono and the rule for the h and v maps
        if is_epi(new_g,i,j,k,l):
            new_g,r=get_receptor(new_g,i+1,j+1)
            rl='if the diagonal map is epi then the receptor of the end is 0'
            pr=[('is_epi',i,j,k,l)]
            new_g=add_shadow_zero_obj(new_g,r,rule=rl,prem=pr)
            if not(is_epi(new_g,i+1,j,i+1,j+1)):
                r='if g°f is epi then g is epi'
                new_g=add_epi(new_g,i+1,j,i+1,j+1,rule=r,prem=pr)
            if not(is_epi(new_g,i,j+1,i+1,j+1)):
                r='if g°f is epi then g is epi'
                new_g=add_epi(g,i,j+1,i+1,j+1,rule=r,prem=pr)
        if is_zero_map(new_g,i,j,k,l):
            if is_mono(new_g,i+1,j,k,l) and not(is_zero_map(new_g,i,j,i+1,j)):
                r='if g°f=0 and g is mono then f=0'
                pr=[('is_zero',i,j,k,l),('is_mono',i+1,j,k,l)]
                new_g=add_zero_map(new_g,i,j,i+1,j,rule=r,prem=pr)
            if is_mono(new_g,i,j+1,k,l) and not(is_zero_map(new_g,i,j,i,j+1)):
                r='if g°f=0 and g is mono then f=0'
                pr=[('is_zero',i,j,k,l),('is_mono',i,j+1,k,l)]
                new_g=add_zero_map(new_g,i,j,i,j+1,rule=r,prem=pr)
            if is_epi(new_g,i,j,i+1,j) and not(is_zero_map(new_g,i+1,j,k,l)):
                r='if g°f=0 and f is epi then g=0'
                pr=[('is_zero',i,j,k,l),('is_mono',i,j,i+1,j)]
                new_g=add_zero_map(new_g,i+1,j,k,l,rule=r,prem=pr)
            if is_epi(new_g,i,j,i,j+1) and not(is_zero_map(new_g,i,j+1,k,l)):
                r='if g°f=0 and f is epi then g=0'
                pr=[('is_zero',i,j,k,l),('is_mono',i,j,i,j+1)]
                new_g=add_zero_map(new_g,i,j+1,k,l,rule=r,prem=pr)
        #no exact condition with the diagonal maps? not in practice
    elif k==i and l==j+1:
        if is_mono(new_g,i,j,k,l):
            new_g,r=get_receptor(new_g,i,j)
            new_g,h=get_hhom(new_g,i,j)
            rl='if a horizontal map is mono then the receptor at the origin is 0'
            pr=[('is_mono',i,j,k,l)]
            new_g=add_shadow_zero_obj(new_g,r,rule=rl,prem=pr)
            rl='if a horizontal map is mono then  the h_homology at the origin is 0'
            new_g=add_shadow_zero_obj(new_g,h,rule=rl,prem=pr)
            if is_zero_map(new_g,i-1,j,i,j+1) and not(is_zero_map(new_g,i-1,j,i,j)):
                r='if g°f=0 and g mono then f=0'
                pr=[('is_mono',i,j,k,l),('is_zero',i-1,j,i,j+1)]
                new_g=add_zero_map(new_g,i-1,j,i,j,rule=r,prem=pr)
            if not(is_zero_map(new_g,i,j-1,i,j)):#
                r='if  g is mono and g,f are two horizontal maps (then g°f=0) then f=0'
                pr=[('is_mono',i,j,k,l)]
                new_g=add_zero_map(new_g,i,j-1,i,j,rule=r,prem=pr)
        if is_epi(new_g,i,j,k,l):
            new_g,d=get_donnor(new_g,k,l)
            new_g,h=get_hhom(new_g,k,l)
            pr=[('is_epi',i,j,k,l)]
            r='if a horizontal map is epi then the donnor at the origin is 0'
            new_g=add_shadow_zero_obj(new_g,d,rule=r,prem=pr)
            r='if a horizontal map is epi the the h_homology at the origin is 0'
            new_g=add_shadow_zero_obj(new_g,h,rule=r,prem=pr)
            if is_zero_map(new_g,i,j,i+1,j+1) and not(is_zero_map(new_g,i,j+1,i+1,j+1)):
                r='if g°f=0 and f epi then  g=0'
                pr=[('is_epi',i,j,k,l),('is_zero',i,j,i+1,j+1)]
                new_g=add_zero_map(new_g,i,j+1,i+1,j+1)
            if not(is_zero_map(new_g,i,j+1,i,j+2)):
                r='if f,g are two horizontal maps (then g°f=0) and f is epi then g=0'
                pr=[('is_epi',i,j,k,l)]
                new_g=add_zero_map(new_g,i,j+1,i,j+2,rule=r,prem=pr)
        if is_zero_map(new_g,i,j,k,l):
            pr=[('is_zero',i,j,k,l)]
            if not(is_zero_map(new_g,i,j,i+1,j+1)):
                r='if g=0 then g°f=0'
                new_g=add_zero_map(new_g,i,j,i+1,j+1,rule=r,prem=pr)
            if not(is_zero_map(new_g,i-1,j,i,j+1)):
                r='if f=0 then g°f=0'
                new_g=add_zero_map(new_g,i-1,j,i,j+1,rule=r,prem=pr)

        new_g=propagate_info_exact(new_g,i,j,i,j+1,i,j+2)
        new_g=propagate_info_exact(new_g,i,j-1,i,j,i,j+1)
    elif k==i+1 and l==j:
        if is_mono(new_g,i,j,k,l):
            new_g,r=get_receptor(new_g,i,j)
            new_g,v=get_vhom(new_g,i,j)
            pr=[('is_mono',i,j,k,l)]
            rl='if a vertical map is mono then the receptor at the origin is 0'
            new_g=add_shadow_zero_obj(new_g,r,rule=rl,prem=pr)
            rl='if a vertical map is mono then the v_homolgy at the origin is 0'
            new_g=add_shadow_zero_obj(new_g,v,rule=rl,prem=pr)
            if is_zero_map(new_g,i,j-1,i+1,j) and not(is_zero_map(new_g,i,j-1,i,j)):
                r='if g°f=0 and g mono then f=0'
                pr=[('is_mono',i,j,k,l),('is_zero',i,j-1,i+1,j)]
                new_g=add_zero_map(new_g,i,j-1,i,j,rule=r,prem=pr)
            if not(is_zero_map(new_g,i-1,j,i,j)):
                r='if f,g are two vertical maps (then g°f=0) and g is mono then g=0'
                pr=[('is_mono',i,j,k,l)]
                new_g=add_zero_map(new_g,i-1,j,i,j,rule=r,prem=pr)
        if is_epi(new_g,i,j,k,l):
            new_g,d=get_donnor(new_g,k,l)
            new_g,v=get_vhom(new_g,k,l)
            pr=[('is_epi',i,j,k,l)]
            r='if a vertical map is epi then the donnor at the end is 0'
            new_g=add_shadow_zero_obj(new_g,d,rule=r,prem=pr)
            r='if a vertical map is epi then v_homology at the end is 0'
            new_g=add_shadow_zero_obj(new_g,v,rule=r,prem=pr)
            if is_zero_map(new_g,i,j,i+1,j+1) and not(is_zero_map(new_g,i+1,j,i+1,j+1)):
                r='if g°f=0 and f is epi then g=0'
                pr=[('is_epi',i,j,k,l),('is_zero',i,j,i+1,j+1)]
                new_g=add_zero_map(new_g,i+1,j,i+1,j+1,rule=r,prem=pr)
            if not(is_zero_map(new_g,i+1,j,i+2,j)):
                r='if f,g are two vertical maps (then g°f=0) and f is epi then g=0'
                pr=[('is_epi',i,j,k,l)]
                new_g=add_zero_map(new_g,i+1,j,i+2,j,rule=r,prem=pr)
        if is_zero_map(new_g,i,j,k,l):
            pr=[('is_zero',i,j,k,l)]
            if not(is_zero_map(new_g,i,j-1,i+1,j)):
                r='if g=0 then g°f=0'
                new_g=add_zero_map(new_g,i,j-1,i+1,j,rule=r,prem=pr)
            if not(is_zero_map(new_g,i,j,i+1,j+1)):
                r='if f=0 then g°f=0'
                new_g=add_zero_map(new_g,i,j,i+1,j+1,rule=r,prem=pr)
        new_g=propagate_info_exact(new_g,i,j,i+1,j,i+2,j)
        new_g=propagate_info_exact(new_g,i-1,j,i,j,i+1,j)
    return new_g

def propagate_info_exact(g,i,j,k,l,m,n):
    new_g=g
    ex=exact(new_g)
    if is_dec_map(new_g,i,j,k,l) and is_dec_map(new_g,k,l,m,n) and (i,j,k,l,m,n) in ex:
        if is_zero_map(new_g,i,j,k,l) and not(is_mono(new_g,k,l,m,n)):
            r='if f,g is exact and f=0 then g is mono'
            pr=[('is_exact',i,j,k,l,m,n),('is_zero',i,j,k,l)]
            new_g=add_mono(new_g,k,l,m,n,rule=r,prem=pr)
        if is_mono(new_g,k,l,m,n) and not(is_zero_map(new_g,i,j,k,l)):
            r='if f,g is exact and g is mono then f=0'
            pr=[('is_exact',i,j,k,l,m,n),('is_mono',k,l,m,n)]
            new_g=add_zero_map(new_g,i,j,k,l,rule=r,prem=pr)
        if is_zero_map(new_g,k,l,m,n) and not(is_epi(new_g,i,j,k,l)):
            r='if f,g is exact and g=0 then f is epi'
            pr=[('is_exact',i,j,k,l,m,n),('is_zero',k,l,m,n)]
            new_g=add_epi(new_g,i,j,k,l,rule=r,prem=pr)
        if is_epi(new_g,i,j,k,l) and not(is_zero_map(new_g,k,l,m,n)):
            r='if f,g is exact and f is epi then g=0'
            pr=[('is_exact',i,j,k,l,m,n),('is_epi',i,j,k,l)]
            new_g=add_zero_map(new_g,k,l,m,n)
    return new_g

def propagate_info_shadow(g):
    shad=shadow_gr(g)
    hhom=homh_num(g)
    vhom=homv_num(g)
    new_g=g

    for (i,j) in hhom:
        h=hhom[i,j]
        if is_dec(new_g,i,j) and gr.is_zero(shad,h) and not(is_dec_exact(new_g,i,j-1,i,j,i,j+1)):
            r='if the h_homology is 0 then the horizontal composition is exact'
            pr=[('is_zero_obj_shad',h)]
            new_g=add_exact_horiz(new_g,i,j,rule=r,prem=pr)
    for (i,j) in vhom:
        v=vhom[i,j]
        if is_dec(new_g,i,j) and gr.is_zero(shad,v) and not(is_dec_exact(new_g,i-1,j,i,j,i+1,j)):
            r='if the v_homology is 0 then the vertical composition is exact'
            pr=[('is_zero_obj_shad',v)]
            new_g=add_exact_verti(new_g,i,j,rule=r,prem=pr)
    return new_g

#########
def connecting_morphism_sequences(g):#compute the possible conecting morphism,
    lab=lbl(g)
    h=homh_num(g)
    v=homv_num(g)
    dep_h=[]
    end_h=[]
    dep_v=[]
    end_v=[]
    hconnect=[]
    vconnect=[]
    hvconnect=[]
    vhconnect=[]
    res=[]
    new_g=g
    shad=shadow_gr(new_g)

    for (i,j) in lab:
        #the second condition is because there is no use to conect things with a zero morphism
        if is_zero_obj(g,i,j+1) and not(is_epi(g,i,j-1,i,j)):
            dep_h.append((i,j))
        if is_zero_obj(g,i,j-1) and not(is_mono(g,i,j,i,j+1)):
            end_h.append((i,j))
        if is_zero_obj(g,i+1,j) and not(is_epi(g,i-1,j,i,j)):
            dep_v.append((i,j))
        if is_zero_obj(g,i-1,j) and not(is_mono(g,i,j,i+1,j)):
            end_v.append((i,j))

    
    for (a,b) in dep_h:
        for (c,d) in end_h:
            if (a,b)!=(c,d):
                bl,new_shad=gr.are_iso_obj(shad,h[a,b],h[c,d])
                if bl:
                    new_g=add_new_shad(new_g,new_shad)#to get the proof of the iso
                    hconnect.append((a,b,c,d))
        for (c,d) in end_v:
            if (a,b)!=(c,d):

                bl,new_shad=gr.are_iso_obj(shad,h[a,b],v[c,d])
                if bl:
                    new_g=add_new_shad(new_g,new_shad)
                    hvconnect.append((a,b,c,d))
    for (a,b) in dep_v:
        for (c,d) in end_h:
            if (a,b)!=(c,d):
                bl,new_shad=gr.are_iso_obj(shad,v[a,b],h[c,d])
                if bl:
                    new_g=add_new_shad(new_g,new_shad)
                    vhconnect.append((a,b,c,d))
        for (c,d) in end_v:
            if (a,b)!=(c,d):
                bl,new_shad=gr.are_iso_obj(shad,v[a,b],v[c,d])
                if bl:
                    new_g=add_new_shad(new_g,new_shad)
                    vconnect.append((a,b,c,d))

    rl='if A->B->0 and 0->C->D are part of the complex and homology at B iso homology at C then there is connecting morphism such that the sequence is exact'
    for (a,b,c,d) in hconnect:
        statement=('is_exact(connected)',a,b-1,a,b,c,d,c,d+1)
        prem=[('are_iso_obj',h[a,b],h[c,d])]
        new_g=add_proof(new_g,statement,rl,prem)
        res.append([a,b-1,a,b,c,d,c,d+1])

    for (a,b,c,d) in hvconnect:
        statement=('is_exact(connected)',a,b-1,a,b,c,d,c+1,d)
        prem=[('are_iso_obj',h[a,b],v[c,d])]
        new_g=add_proof(new_g,statement,rl,prem)
        res.append([a,b-1,a,b,c,d,c+1,d])
    for (a,b,c,d) in vhconnect:
        statement=('is_exact(connected)',a-1,b,a,b,c,d,c,d+1)
        prem=[('are_iso_obj',v[a,b],h[c,d])]
        new_g=add_proof(new_g,statement,rl,prem)
        res.append([a-1,b,a,b,c,d,c,d+1])
    for (a,b,c,d) in vconnect:
        statement=('is_exact(connected)',a-1,b,a,b,c,d,c+1,d)
        prem=[('are_iso_obj',v[a,b],v[c,d])]
        new_g=add_proof(new_g,statement,rl,prem)
        res.append([a-1,b,a,b,c,d,c+1,d])
    return res,new_g
    
########
''' the statements are of the following form:
('are_iso_obj',i,j): the object number i and number j in the shadow graph are ismorphic
('is_zero_obj',i,j): the object at (i,j) is 0
('is_zero_obj_shad,i): the object number i in the shadow graph is 0
('is_mono',i,j,k,l): the map (i,j)->(k,l) is a mono
('is_epi',i,j,k,l): the map (i,j)->(k,l) is an epi
('is_iso',i,j,k,l): the map (i,j)->(k,l) is an iso
('is_zero',i,j,k,l): the map (i,j)->(k,l) is the zero map
('is_exact',i,j,k,l,m,n): the composition (i,j)-> (k,l) and (k,l)->(m,n) is exact
('is_exact(connected)',a,b,c,d,e,f,g,h): there is a conection morphism \del (c,d)->(e,f) such that the sequence (a,b)->(c,d) ->(e,f)->(g,h)

'''
def aff_statement(g,statement):
    n=len(statement)
    lab=lbl(g)
    if n==2:
        (prop,x)=statement
        print(prop)
        shad=shadow_gr(g)
        lab_shad=gr.lbl(shad)
        print(lab_shad[x],prop)
    if n==3:
        (prop,i,j)=statement
        if prop=='are_iso_obj':
            shad=shadow_gr(g)
            lab_shad=gr.lbl(shad)
            print(lab_shad[i],' and ',lab_shad[j],prop)
        else:
            name=lab.get((i,j),"ZERO")
            print(name,prop,end='')
    elif n==5:
        (prop,i,j,k,l)=statement
        o=lab.get((i,j),"ZERO")
        t=lab.get((k,l),"ZERO")
        print(o,'->',t,prop,end='')
    elif n==7:
        (prop,i,j,k,l,m,n)=statement
        a=lab.get((i,j),"ZERO")
        b=lab.get((k,l),"ZERO")
        c=lab.get((m,n),"ZERO")
        print(a,'->',b,'->',c,prop,end='')
    elif n==9:
        (prop,a,b,c,d,e,f,h,i)=statement
        A=lab.get((a,b),"ZERO")
        B=lab.get((c,d),"ZERO")
        C=lab.get((e,f),"ZERO")
        D=lab.get((h,i),"ZERO")
        print(A,'->',B,'->',C,'->',D,prop,en='')

def proof_origin(g,s):#it's there to check if it's a proof from the shadow graph, and just extract the proof if it's normal
    if len(s)==3:
        (prop,_,_)=s
        if prop=='are_iso_obj':
            return ('shadow',[])
    if len(s)==2:
        (prop,_)=s
        if prop=='is_zero_obj_shad':
            return ('shadow',[])
    pf=proof(g)
    return pf.get(s,('',[]))

def aff_proof(g,statement):
    _,g=connecting_morphism_sequences(g)
    pf=proof(g)
    (rule,_)=pf.get(statement,('NOT',[]))
    if rule=='NOT':
        aff_statement(g,statement)
        print(' is not proven')
        return 

    shad=shadow_gr(g)
    marked=dict()
    def explore(statement):
        m=marked.get(statement,False)
        if not(m):
            #print(statement)
            marked[statement]=True
            (rule,prem)=proof_origin(g,statement)
            if prem==[]:
                if rule=='shadow':
                    if len(statement)==2:
                        (_,x)=statement
                        #it is mandatory to translate the statment into the language of the shadow graph
                        gr.aff_proof(shad,('is_zero_obj',x),lbl(g))
                    else:
                        #it's then a statement of isomorphism between two objects
                        gr.aff_proof(shad,statement,lbl(g))
                else:
                    aff_statement(g,statement)
                    print(' by assumption')
                    print()
            else:
                for x in prem:
                    explore(x)
                aff_statement(g,statement)
                print(' because: ',rule,'applied to :')
                for x in prem:
                    print("* ",end='')
                    aff_statement(g,x)
                    print('')
                print('')
    explore(statement)

def new_facts(g):#the things that are not an hypothesis, a lot of things are trivial
    pf=proof(g)
    facts=[]
    for x in pf:
        if pf[x] != (' by assumption',[]):
            facts.append(x)
    for k in range(len(facts)):
        print('fact',str(k),':')
        aff_statement(g,facts[k])
        print()
    return facts

def aff(grid):
    labl=lbl(grid)
    for (i,j) in labl:
        og=labl[i,j]
        tg1=labl.get((i+1,j),"ZERO")
        tg2=labl.get((i,j+1),"ZERO")

        if tg1 != "ZERO":
            if is_zero_map(grid,i,j,i+1,j):
                print("zero,",end='')
            if is_mono(grid,i,j,i+1,j) and is_epi(grid,i,j,i+1,j):
                print("iso,",end='')
            elif is_mono(grid,i,j,i+1,j):
                print("mono,",end='')
            elif is_epi(grid,i,j,i+1,j):
                print("epi,",end='')
            print(og+"->"+tg1)

        if tg2 != "ZERO":
            if is_zero_map(grid,i,j,i,j+1):
                print("zero,",end='')
            if is_mono(grid,i,j,i,j+1) and is_epi(grid,i,j,i,j+1):
                print("iso,",end='')
            elif is_mono(grid,i,j,i,j+1):
                print("mono,",end='')
            elif is_epi(grid,i,j,i,j+1):
                print("epi,",end='')
            print(og+"->"+tg2)
    ex=exact(grid)

    print()
    print("EXACT CONDITION")

    for (i,j,k,l,m,n) in ex:
        ij=labl.get((i,j),"ZERO")
        kl=labl.get((k,l),"ZERO")
        mn=labl.get((m,n),"ZERO")
        if not(ij=="ZERO" and mn=="ZERO"):
            print("EXACT:"+ij+"->"+kl+"->"+mn)
    
    print()
    print("CONECTING MORPHISM")
    conect,_=connecting_morphism_sequences(grid)
    for (x,y,a,b,c,d,z,w) in conect:
        A=labl.get((x,y),"ZERO")
        B=labl.get((a,b),"ZERO")
        C=labl.get((c,d),"ZERO")
        D=labl.get((z,w),"ZERO")

        print("EXACT:"+A+"->"+B+"->"+C+"->"+D)

#aff_proof(sfl(),('is_iso',0,1,1,1))
#aff_proof(fl_inj(),('is_mono',0,2,1,2))
#aff_proof(snake(),('is_exact(connected)',-1,1,-1,2,2,0,2,1))
