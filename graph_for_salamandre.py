''' a graph will be given by:
    * the function origin, 
    * the function taill (for the edges) 
    * a label function 
    * a list of exactness conditions
    * the function that tells if a map is zero
    * if a map is mono
    * if a map is epi, 
    *if an object is zero
    *a dictionary that keeps track of th proof,
    proof[facts]=(rule applied,[list of premises])
    => be carefull to write down uniformly the statement of the facts:(see the list befor aff_statment)
    *
'''
### DATA

def numb_v(g):#gives the number of vertex
    (_,_,lbl,_,_,_,_,_,_)=g
    return len(lbl)
def numb_e(g):#gives the number of edges
    (orig,_,_,_,_,_,_,_,_)=g
    return len(orig)
def ori(g):#gives the map of origins numbers
    (og,_,_,_,_,_,_,_,_)=g
    return og
def tail(g):#gives the map of tail numbers
    (_,tg,_,_,_,_,_,_,_)=g
    return tg
def lbl(g):#gives the labels of the vertex
    (_,_,lbl,_,_,_,_,_,_)=g
    return lbl
def exact(g):#gives the list of exactness conditions (two arrows)
    (_,_,_,exact,_,_,_,_,_)=g
    return exact
def zero_map(g):#gives the boolean list of zero maps
    (_,_,_,_,zero,_,_,_,_)=g
    return zero
def mono_map(g):#gives the boolean list of mono maps
    (_,_,_,_,_,mono,_,_,_)=g
    return mono
def epi_map(g):#gives the boolean list of epi maps
    (_,_,_,_,_,_,epi,_,_)=g
    return epi
def zero_obj(g):#gives the boolean list of zero objects
    (_,_,_,_,_,_,_,z_o,_)=g
    return z_o
def proof(g):#gives the dictionary of proof
    (_,_,_,_,_,_,_,_,pf)=g
    return pf

### CONSTRUCTIONS

def get_arrow(g,o,t):
    a=-1
    ne=numb_e(g)
    og=ori(g)
    tg=tail(g)

    found=False
    while not(found) and a<ne-1:
        a=a+1
        found=(og[a]==o and tg[a]==t)
    
    if found:
        return a
    else:
        return -1

def graph_void():#gives a graph with nothing 
    return ([],[],[],[],[],[],[],[],dict())

#in order to keep track of the proofs no label should be added by this two functions except the hypothesis

def add_vertex(g,new_lbl,is_zero=False):#add one vertex with the label lbl
    (og,tg,lab,exact,zero,mono,epi,zobj,pf)=g
    nb_v=len(lab)
    lab.append(new_lbl)
    zobj.append(False)
    new_g=(og,tg,lab,exact,zero,mono,epi,zobj,pf)
    if is_zero:
        new_g=add_zero_obj(new_g,nb_v)
    return (new_g,nb_v)

def add_edge(g,o,t,e=-1,is_zero=False,is_mono=False,is_epi=False):#take a graph g and add an arrow from o to t
    new_g=g
    if e== -1:
        e=get_arrow(new_g,o,t)
    if e == -1:
        if o==t:
            return (g,-1)
        (og,tg,labl,exact,zero,mono,epi,zobj,pf)=g
        e=numb_e(g)
        tg.append(t)
        og.append(o)
        zero.append(False)
        mono.append(False)
        epi.append(False)
        new_g=(og,tg,labl,exact,zero,mono,epi,zobj,pf)
        new_g=propagate_info(new_g,e)#

    #the test will be donne un the function
    if is_zero:
        new_g=add_zero(new_g,e)
    if is_mono:
        new_g=add_mono(new_g,e)
    if is_epi:
        new_g=add_epi(new_g,e)
    
    return (new_g,e) 

#before propagating it's important to check that an info is not new because otherwise there is a loop with the propagation

def add_exact(g,num1,num2,rule=' by assumption',prem=[]):#the compositions num2°num1 is now exact
    #the map og[num1]->tg[num2] is added and is now zero
    (og,tg,labl,ex,zero,mono,epi,zobj,pf)=g
    new_g=g
    x=og[num1]
    z=tg[num2]


    if not (num1,num2) in ex:
        ex.append((num1,num2))
        pf[('is_exact',num1,num2)]=(rule,prem)
        new_g=(og,tg,labl,ex,zero,mono,epi,zobj,pf)

        (new_g,new_e)=add_edge(new_g,x,z)
        r='if f,g is exact then g°f=0'
        pr=[('is_exact',num1,num2)]
        new_g=add_zero(new_g,new_e,rule=r,prem=pr)
    return new_g

def add_mono(g,f,rule=' by assumption',prem=[]):#the arrow f is now a mono
    (og,tg,labl,exact,zero,mono,epi,zobj,pf)=g
    if not(mono[f]):
        mono[f]=True
        pf[('is_mono',f)]=(rule,prem)
        new_g=(og,tg,labl,exact,zero,mono,epi,zobj,pf)
        if epi[f]:
            stat=('is_iso',f)
            rl='if f is a mono and an epi then f is an iso'
            pr=[('is_mono',f),('is_epi', f)]
            new_g=add_proof(new_g,stat,rl,pr)
        new_g=propagate_info(new_g,f)
        return new_g
    return g

def add_epi(g,f,rule=' by assumption',prem=[]):#the arrow f is now an epi
    (og,tg,labl,exact,zero,mono,epi,zobj,pf)=g
    if  not(epi[f]):
        epi[f]=True
        pf[('is_epi',f)]=(rule,prem)
        new_g=(og,tg,labl,exact,zero,mono,epi,zobj,pf)
        if mono[f]:
            stat=('is_iso',f)
            rl='if f is a mono and an epi then f is an iso'
            pr=[('is_mono',f),('is_epi', f)]
            new_g=add_proof(new_g,stat,rl,pr)
        new_g=propagate_info(new_g,f)
        return new_g
    return g

def add_zero(g,f,rule=' by assumption',prem=[]):#the arrow f is now a zero mapp
    (og,tg,lbl,exact,zero,mono,epi,zobj,pf)=g
    if not(zero[f]):
        zero[f]=True
        pf[('is_zero',f)]=(rule,prem)
        new_g=(og,tg,lbl,exact,zero,mono,epi,zobj,pf)
        new_g=propagate_info(new_g,f)
        return new_g
    return g

def add_zero_obj(g,x,rule=' by assumption',prem=[]):
    (og,tg,labl,ex,zero,mono,epi,zobj,pf)=g
    if not(zobj[x]):
        zobj[x]=True
        pf[('is_zero_obj',x)]=(rule,prem)
        new_g=(og,tg,labl,ex,zero,mono,epi,zobj,pf)
        ne=numb_e(new_g)
        for f in range(ne):
            if not(zero[f]) and (og[f]==x):
                r='if X=0 then f:X->Y=0'
                pr=[('is_zero_obj',x)]
                new_g=add_zero(new_g,f,rule=r,prem=pr)
            if not(zero[f]) and (tg[f]==x):
                r='if Y=0 then f:X->Y'
                pr=[('is_zero_obj',x)]
                new_g=add_zero(new_g,f,rule=r,prem=pr)
        return new_g
    return g

def add_proof(g,statement,rule,prem):
    (og,tg,labl,ex,zero,mono,epi,zobj,pf)=g
    pf[statement]=(rule,prem)
    new_g=(og,tg,labl,ex,zero,mono,epi,zobj,pf)
    return new_g

### COMPUTATION

def propagate_info_trgl(gr,f,g,gf):#use the rules to add info on the triangle, assume that g°f=gf
    #it's important to check that an info is not new because otherwise there is a loop with the propagation 

    mono=mono_map(gr)
    epi=epi_map(gr)
    zero=zero_map(gr)
    new_g=gr
    if zero[f] and not(zero[gf]):
        r='if f=0 then g°f=0'
        pr=[('is_zero',f)]
        new_g=add_zero(new_g,gf,rule=r,prem=pr)
    if zero[g] and not(zero[gf]):
        r='if g=0 then g°f=0'
        pr=[('is_zero',g)]
        new_g=add_zero(new_g,gf,rule=r,prem=pr)
    if mono[g] and mono[f] and not(mono[gf]):
        r='if f is mono and g is mono then g°f is mono'
        pr=[('is_mono',f),('is_mono',g)]
        new_g=add_mono(new_g,gf,rule=r,prem=pr)
    if mono[gf] and not(mono[f]):
        r='if g°f is mono then f is mono'
        pr=[('is_mono',gf)]
        new_g=add_mono(new_g,f,rule=r,prem=pr)
    if epi[g] and epi[f] and not(epi[gf]):
        r='if f is epi and g is epi then g°f is epi'
        pr=[('is_epi',f),('is_epi',g)]
        new_g=add_epi(new_g,gf,rule=r,prem=pr)
    if epi[gf] and not(epi[g]):
        r='if g°f is epi then g epi'
        pr=[('is_epi',gf)]
        new_g=add_epi(new_g,g,rule=r,prem=pr)
    if zero[gf] and mono[g] and not(zero[f]):
        r='if g is mono and g°f=0 then f=0'
        pr=[('is_zero',gf),('is_mono',g)]
        new_g=add_zero(new_g,f,rule=r,prem=pr)
    if zero[gf] and epi[f] and not(zero[g]):
        r='if f is epi and g°f=0 then g=0'
        pr=pr=[('is_zero',gf),('is_epi',f)]
        new_g=add_zero(new_g,g,rule=r,prem=pr)
            
    #the condition zero[gf] is there to avoid checking in ex if not necessary
    ex=exact(new_g)
    if zero[gf] and zero[f] and not(mono[g]) and (f,g) in ex : 
        r='if f,g is exact and f=0 then g is mono'
        pr=[('is_zero',f),('is_exact',f,g)]
        new_g=add_mono(new_g,g,rule=r,prem=pr)
    if zero[gf] and zero[g] and not(epi[f]) and (f,g) in ex : 
        r='if f,g is exact and g=0 then f is epi'
        pr=[('is_zero',g),('is_exact',f,g)]
        new_g=add_epi(new_g,f,rule=r,prem=pr)
    if zero[gf] and mono[g] and not(zero[f]) and (f,g) in ex:
        r='if f,g is exact and g is mono then f=0'
        pr=[('is_mono',g),('is_exact',f,g)]
        new_g=add_zero(new_g,f,rule=r,prem=pr)
    if zero[gf] and epi[f] and not(zero[g]) and (f,g) in ex:
        r='if f,g is exact and f is epi then g=0'
        pr=[('is_epi',f),('is_exact',f,g)]
        new_g=add_zero(new_g,g)
    return new_g

def propagate_info(gr,f):#use the rules to add info on f
    epi=epi_map(gr)
    zero=zero_map(gr)
    mono=mono_map(gr)
    og=ori(gr)
    tg=tail(gr)
    zobj=zero_obj(gr)
    new_g=gr

    if zobj[og[f]] and not(mono[f]):
        r='if X=0 then f:X->Y is mono'
        pr=[('is_zero_obj',og[f])]
        new_g=add_mono(new_g,f,rule=r,prem=pr)
    if zobj[og[f]] and not(zero[f]):
        r='if X=0 then f:X->Y=0'
        pr=[('is_zero_obj',og[f])]
        new_g=add_zero(new_g,f,rule=r,prem=pr)
    if zobj[tg[f]] and not(epi[f]):
        r='if Y=0 then f:X->Y is epi'
        pr=[('is_zero_obj',tg[f])]
        new_g=add_epi(new_g,f,rule=r,prem=pr)
    if zobj[tg[f]] and not(zero[f]):
        r='if Y=0 then f:X->Y=0'
        pr=[('is_zero_obj',tg[f])]
        new_g=add_zero(new_g,f,rule=r,prem=pr)   
    if epi[f] and zero[f] and not(zobj[tg[f]]):
        r='if f:X->Y is 0 and epi then Y=0'
        pr=[('is_zero',f),('is_epi',f)]
        new_g=add_zero_obj(new_g,tg[f],rule=r,prem=pr)
    if mono[f] and zero[f] and not(zobj[og[f]]):
        r='if f:X->Y is 0 and mono then X=0'
        pr=[('is_zero',f),('is_mono',f)]
        new_g=add_zero_obj(new_g,og[f],rule=r,prem=pr)
    # The two previous cases includes the cases where an object is iso to a zero object
    
    ne=numb_e(new_g)

    for a in range(ne):
        if og[a]==og[f]:
            b=get_arrow(new_g,tg[f],tg[a])#to optimize but latter
            if b== -1:
                b=get_arrow(new_g,tg[a],tg[f])
                if b != -1:
                    new_g=propagate_info_trgl(new_g,a,b,f)
            else:
                new_g=propagate_info_trgl(new_g,f,b,a)
        if tg[a]==tg[f]:
            b=get_arrow(new_g,og[f],og[a])#to optimize but latter
            if b== -1:
                b=get_arrow(new_g,og[a],og[f])
                if b != -1:
                    new_g=propagate_info_trgl(new_g,b,f,a)
            else:
                new_g=propagate_info_trgl(new_g,b,a,f)
    return new_g

######## test (for using in the salamander file)
def is_zero(g,x):
    z=zero_obj(g)
    return z[x]

def is_zero_map(g,f):
    z=zero_map(g)
    return z[f]

def is_iso_map(g,f):
    mono=mono_map(g)
    epi=epi_map(g)
    return (epi[f] and mono[f])

def are_iso_obj(gr,dep,end):
    #(isog,new_g)=iso_graph(gr)
    marked=[False for k in range(numb_v(gr))]

    prem=[]
    def explore(x,g):
        if not(marked[x]):
            marked[x]=True
            og=ori(g)
            tg=tail(g)
            ne=numb_e(g)
            for f in range(ne):
                if is_iso_map(g,f):
                    if og[f]==x:
                        if tg[f]==end:
                            return (True,[('is_iso',f)])
                        (b,prm)=explore(tg[f],g)
                        if b:
                            res=prm.copy()
                            res.append(('is_iso',f))
                            return (True, res)
                    if tg[f]==x:
                        if og[f]==end:
                            return (True,[('is_iso',f)])
                    #print(og[f])
                        (b,prm)=explore(og[f],g)
                        if b:
                            res=prm.copy()
                            res.append(('is_iso',f))
                            return (True,res)
        return (False,[])
    
    (b,prem)=explore(dep,gr)
    new_g=gr
    if b:
        stat=('are_iso_obj',dep,end)
        rl='if there is a chain of isomorphism between X and Y then they are isomorphic'
        new_g=add_proof(new_g,stat,rl,prem)
    return (b,new_g)
#######

# a function to disply the graph g and the information that can be computed
def aff(g):
    nv=numb_v(g)
    ne=numb_e(g)
    o=ori(g)
    t=tail(g)
    labl=lbl(g)
    zero=zero_map(g)
    mono=mono_map(g)
    epi=epi_map(g)
    zobj=zero_obj(g)

    print(nv," vertex")
    print("")

    for k in range(nv):
        if zobj[k] and labl[k] !="ZERO":
            print("ZERO:",labl[k])

    print(ne," edges")
    print("")
    for k in range(ne):
            if zero[k]:
                print("zero,",end=' ')
            if mono[k] and epi[k]:
                print("iso,",end=' ')
            elif epi[k]:
                print("epi,",end=' ')
            elif mono[k]:
                print("mono,",end=' ')
            print(labl[o[k]]+"->"+labl[t[k]])
    
    print("")

    for (x,y)in exact(g):
        print("EXACT: "+labl[o[x]]+"->"+labl[t[x]]+"->"+labl[t[y]])

''' the statements are of the following form:
('are_iso_obj,i,j): the objects number i and j are isomorphic
('is_zero_obj',i): the object number i  is 0
('is_mono',f): the map number f  is a mono
('is_epi',f): the map number f is an epi
('is_iso',f): the map number f is an iso
('is_zero',f): the map number f is the zero map
('is_exact',f,g): the composition (f,g) is exact

or a statment from the original graph (from salamander file)
('is_exact,i,j,k,l,m,n): the composition (i,j)->(k,l)->(m,n) is exact
'''

def aff_statement(gr,statement,lab_g_dep):
    n=len(statement)
    lab=lbl(gr)
    og=ori(gr)
    tg=tail(gr)
    if n==2:
        (prop,x)=statement
        if prop=='is_zero_obj':
            name=lab[x]
            print(name,'is_zero_obj',end='')
        else:
            #print(statement)
            o=og[x]
            t=tg[x]
            print(lab[o],'->',lab[t],prop,end='')

    elif n==3:
        (prop,f,g)=statement
        if prop=='is_zero_obj':
            name=lab_g_dep.get((f,g),"ZERO")
            print(name,prop,end='')
        elif prop=='are_iso_obj':
            print(lab[f],' and ',lab[g],prop)
        else:#then it's an exact statement
            print(lab[og[f]],'->',lab[tg[f]],'->',lab[tg[g]],prop,end='')
    elif n==7:
        #it's an exact statement from the original graph
        (prop,i,j,k,l,m,n)=statement
        a=lab_g_dep.get((i,j),"ZERO")
        b=lab_g_dep.get((k,l),"ZERO")
        c=lab_g_dep.get((m,n),"ZERO")
        print(a,'->',b,'->',c,prop,end='')

#the lab_g_dep is for using this file inside salamander
def aff_proof(g,statement,lab_g_dep=dict()):
    pf=proof(g)
    (rule,_)=pf.get(statement,('NOT',[]))
    if rule=='NOT':
        aff_statement(g,statement,lab_g_dep)
        print(' is not proven')
        return 

    marked=dict()
    def explore(statement):
        m=marked.get(statement,False)
        if not(m):
            marked[statement]=True
            (rule,prem)=pf.get(statement,(' by assumption',[]))
            #inside a proof, if something is not recorded, then the statement came from the file salamander, then either it's by assumption or it has some premices 
            if prem==[]:
                aff_statement(g,statement,lab_g_dep)
                print(rule)
                print()
            else:
                for x in prem:
                    explore(x)
                aff_statement(g,statement,lab_g_dep)
                print(' because: ',rule,'applied to :')
                for x in prem:
                    print("* ",end='')
                    aff_statement(g,x,lab_g_dep)
                    print()
                print()
    explore(statement)

### EXAMPLES AND TESTS
def graph1():
    g=graph_void()
    g,x=add_vertex(g,"1")
    g,y=add_vertex(g,"2")
    g,z=add_vertex(g,"3")
    g,w=add_vertex(g,"4")
    (g,_)=add_edge(g,x,y,is_mono=True,is_epi=True)
    (g,_)=add_edge(g,z,y,is_mono=True,is_epi=True)
    (g,_)=add_edge(g,z,w,is_mono=True,is_epi=True)

    return g

def sfl():
    g=graph_void()

    g,a=add_vertex(g,"1")
    g,b=add_vertex(g,"2")
    g,c=add_vertex(g,"3")
    g,d=add_vertex(g,"4")
    g,e=add_vertex(g,"5")
    g,f=add_vertex(g,"6")

    (g,e1)=add_edge(g,a,b,is_mono=True)
    (g,e2)=add_edge(g,b,c,is_epi=True)
    (g,e3)=add_edge(g,d,e,is_mono=True)
    (g,e4)=add_edge(g,e,f,is_epi=True)
    (g,_)=add_edge(g,a,d,is_mono=True,is_epi=True)
    (g,_)=add_edge(g,c,f,is_mono=True,is_epi=True)
    (g,_)=add_edge(g,b,e)

    g=add_exact(g,e1,e2)
    g=add_exact(g,e3,e4)

    return g

def fl_inj():
    g=graph_void()
    g,x=add_vertex(g,"1")
    g,y=add_vertex(g,"2")
    g,z=add_vertex(g,"3")
    g,w=add_vertex(g,"4")
    g,u=add_vertex(g,"5")
    g,v=add_vertex(g,"6")
    g,s=add_vertex(g,"7")
    g,t=add_vertex(g,"8")
    (g,e1)=add_edge(g,x,y)
    (g,e2)=add_edge(g,y,z)#,is_zero=True)
    (g,e3)=add_edge(g,z,w)

    (g,e4)=add_edge(g,u,v)
    (g,e5)=add_edge(g,v,s)
    (g,e6)=add_edge(g,s,t)

    (g,_)=add_edge(g,x,u,is_epi=True)
    (g,_)=add_edge(g,y,v,is_mono=True)
    (g,_)=add_edge(g,z,s)
    (g,_)=add_edge(g,w,t,is_mono=True)

    g=add_exact(g,e1,e2)
    g=add_exact(g,e2,e3)
    g=add_exact(g,e4,e5)
    g=add_exact(g,e5,e6)
    
    return g

def test():
    g=graph_void()
    g,x=add_vertex(g,"1")
    g,y=add_vertex(g,"2")
    g,z=add_vertex(g,"3")

    g,e=add_edge(g,x,y)
    g,f=add_edge(g,y,z,is_epi=True)
    g=add_exact(g,e,f)

    return g

def pb():
    g=graph_void()
    g,x=add_vertex(g,"1")
    g,y=add_vertex(g,"2")
    g,z=add_vertex(g,"3")
    g,v=add_vertex(g,"4")

    (g,e1)=add_edge(g,x,v)
    g,_=add_edge(g,x,y,is_zero=True)
    (g,e2)=add_edge(g,y,z)
    (g,e1)=add_edge(g,x,z)
    (g,e2)=add_edge(g,z,v)
    return g