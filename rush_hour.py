from z3 import *
import sys

dimensions=0
max_moves=0
cars=[]
mines=[]
k = 0

with open(sys.argv[1],"r") as file:
    for i,line in enumerate(file):
        if i==0:
            dimensions=int(line.split(",")[0])
            max_moves=int(line.split(",")[1])
            continue
        
        elif i==1:
            line=line.strip()
            nums=line.split(",")
            cars.append([3, int(nums[0]), int(nums[1])])
            k+=1

        else:
            line=line.strip()
            nums=line.split(",")
            cars.append([int(nums[0]), int(nums[1]), int(nums[2])])
            k += 1

if cars[0][2]!=dimensions-2:
    initial_state = Array('initial_state', IntSort(), IntSort())
    n = Int('n')
    n = 0


    def winning_condition(state):
        return (state[2]==dimensions-2)

    for car in cars:
        initial_state = Store(initial_state, n, car[0])
        initial_state = Store(initial_state, n+1, car[1])
        initial_state = Store(initial_state, n+2, car[2])
        n = n + 3


    def unequal(x1, y1, x2, y2, x01, y01, x02, y02):

        a = Or(x1!=x01, y1!=y01)
        b= Or(x2!=x01, y2!=y01)
        c = Or(x1!=x02, y1!=y02)
        d = Or(x2!=x02, y2!=y02)
        return And(a,b,c,d)




    def on_board(state,l):
        cond1= Implies(state[3*l]==0, And(state[3*l+1]<= dimensions-2,state[3*l+2]<=dimensions-1,state[3*l+1]>=0,state[3*l+2]>=0))
        cond2= Implies(Or(state[3*l]==1, state[3*l]==3), And(state[3*l+2]<= dimensions-2,state[3*l+1]<=dimensions-1,state[3*l+2]>=0,state[3*l+1]>=0))
        
        return And(cond1, cond2)



    def valid_state(s,state, l):
        answer = Bool('answer')
        answer = And(1>0, 2>0)
        x1 = Int('x_%s_1'%l)
        y1 = Int('y_%s_1'%l)
        x2 = Int('x_%s_2'%l)
        y2 = Int('y_%s_2'%l)
        s.add(Implies(state[3*l]==0, And(x1==state[3*l+1], y1==state[3*l+2], x2==state[3*l+1]+1, y2==state[3*l+2]) ))
        s.add(Implies(Or(state[3*l]==1, state[3*l]==3), And(x1==state[3*l+1], y1==state[3*l+2], x2==state[3*l+1], y2==state[3*l+2]+1) ))
        # cond5 = Implies(state[3*l]==2, And(x1==state[3*l+1], y1==state[3*l+2], x2==-1, y2==-1))
        # answer = And(answer, cond3, cond4)
        for m in range(len(cars)):
            x01 = Int('x_%s_01_%s'%(l,m))
            y01 = Int('y_%s_01_%s'%(l,m))
            x02 = Int('x_%s_02_%s'%(l,m))
            y02 = Int('y_%s_02_%s'%(l,m))
            s.add(x01==state[3*m+1])
            s.add((y01==state[3*m+2]) )
            s.add(Implies(state[3*m]==0, And(x02==x01+1, y02==y01)))
            s.add(Implies(Or(state[3*m]==1, state[3*m]==3), And(x02==x01, y02==y01+1)))
            s.add(Implies(state[3*m]==2, And(x02==-1, y02==-1)))
            s.add(Implies(l!=m,unequal(x1, y1, x2, y2, x01, y01, x02, y02)))
                # final = And(cond6, cond7, cond10, cond11, cond12, cond13)

                # answer = And(answer, Implies(m!=l, final))
                # answer = And(answer, final)

        # return (simplify(answer))


            


    s = Solver()
    X = [ [ Int("x_%s_%s" % (i, j)) for j in range(2) ]
        for i in range(max_moves) ]
        
    Y = [Array('state_%s'%(i), IntSort(), IntSort()) for i in range(max_moves+1)]
    Y[0] = initial_state
    for l in range(max_moves):
        s.add(And(X[l][0] >= 0, X[l][0] < len(cars)))
        s.add(Y[0][3*X[l][0]]!=2)
        s.add(Or(X[l][1]==1, X[l][1]==-1))
        for m in range(len(cars)):
            s.add(Implies(X[l][0]!=m, And(Y[l+1][3*m]==Y[l][3*m], Y[l+1][3*m+1]==Y[l][3*m+1], Y[l+1][3*m+2]==Y[l][3*m+2])))
            s.add(Implies(And(X[l][0]==m, Y[l][3*m]==0), And(Y[l+1][3*m]==Y[l][3*m], Y[l+1][3*m+1]==Y[l][3*m+1]+X[l][1], Y[l+1][3*m+2]==Y[l][3*m+2])))
            s.add(Implies(And(X[l][0]==m, Or(Y[l][3*m]==1,Y[l][3*m]==3)), And(Y[l+1][3*m]==Y[l][3*m], Y[l+1][3*m+1]==Y[l][3*m+1], Y[l+1][3*m+2]==Y[l][3*m+2]+X[l][1])))
        valid_state(s,Y[l+1], X[l][0])

    for i in range(max_moves-1):
        s.add(Implies(X[i][0]==X[i+1][0], X[i][1]!=-X[i+1][1]))

    for i in range(max_moves):
        s.add(on_board(Y[i+1], X[i][0]))

    answer = Bool('answer')
    answer = False
    for i in range(max_moves+1):
        answer = Or(answer, winning_condition(Y[l]))
    s.add(answer)
    # s.add(winning_condition(Y[max_moves]))

    # m = s.model()
    if s.check()==sat:
        m = s.model()
        r = [ [ m.evaluate(X[i][j]) for j in range(2) ]
            for i in range(max_moves) ]

        for move in r:
            car=cars[move[0].as_long()]
            if car[0]==0:
                d =move[1].as_long()
                if d==1:
                    # if the car isw vertical then move the car down and print the coordinates with 
                    print(str(car[1]+1)+","+str(car[2]))
                    cars[move[0].as_long()][1]+=1

                elif d==-1:
                    print(str(car[1])+","+str(car[2]))
                    cars[move[0].as_long()][1]-=1

            elif car[0]==1 or car[0]==3:
                d= move[1].as_long()
                if d==1:
                    print(str(car[1])+","+str(car[2]+1))
                    cars[move[0].as_long()][2]+=1

                elif d==-1:
                    print(str(car[1])+","+str(car[2]))
                    cars[move[0].as_long()][2]-=1

    else:
        print("unsat")

