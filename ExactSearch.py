import random
import time

class SAT:
    def __init__(self):
 
        self.literals = []
        self.literalsValue = {}
        self.literalsValueComplement = {}
        self.formula = ""
        self.x = ""
        


    '''Generate a list of literals according to the number of literals stated by the user'''
    def LiteralListGenerator(self,numOfLiterals):
        for x in range(1,numOfLiterals + 1):
            self.literals.append("x"+str(x))
        for y in range(1, numOfLiterals + 1):
            self.literals.append("¬x"+str(y))


    '''Generate dictionaries by creating key value pair for each literal''' 
    def DictKeyValueGenerator(self,numOfLiterals):
        for x in range(numOfLiterals,0,-1):
            self.literalsValue["x"+str(x)] = 0
            self.literalsValueComplement["¬x"+str(x)] = 1


    '''Set string x'''
    def SetValueX(self,numOfLiterals):
        self.x = "0"*numOfLiterals


    '''Generate problem randomly according to number of clauses stated by the user'''
    def ProblemGenerator(self,numOfClauses):
        checkList = []
        for x in range (numOfClauses):
            while True:
                temp = self.literals.copy()
                tempCheckList = []

                choice1 = random.choice(temp)
                temp.remove(choice1)
                choice2 = random.choice(temp)
                temp.remove(choice2)
                choice3 = random.choice(temp)

                if x == 0:
                    checkList.append([choice1,choice2,choice3])
                    break

                else:     
                    tempCheckList.append([choice1,choice2,choice3])
                    counter = 0

                    for item in checkList:
                        if set(item) != set(tempCheckList[0]):
                            counter += 1
                        else:
                            counter = 0
                            break
                        
                        
                    if counter > 0:
                        checkList.append([choice1,choice2,choice3])
                        break
                    else:
                        continue
                        

            
            if x != 0:
                self.formula = self.formula + " ∧ "
            self.formula = self.formula + "(" + choice1 +" ∨ " + choice2 +" ∨ " + choice3 + ")"

            
        return self.formula


    '''Assign new value to literals inside dictionary by incrementing 1 in binary form'''
    def AssignValueDictionary(self):
        self.x = ('{:0'+str(_input)+'b}').format(1 + int(self.x, 2))

        original = self.x
        original = original[::-1]
        reverse = list(self.x)
        
        for y in range (len(reverse)):
            if reverse[y] == '0':
                reverse[y] = 'a'
            else:
                reverse[y] = 'b'
                
        for z in range (len(reverse)):
            if reverse[z] == 'a':
                reverse[z] = '1'
            else:
                reverse[z] = '0'

        reverse = "".join(reverse)
        reverse = reverse[::-1]
        
        counter = 0
        for i in self.literalsValueComplement:
            self.literalsValueComplement[i] = int(reverse[counter])
            counter += 1

        counter1 = 0
        for i in self.literalsValue:
            self.literalsValue[i] = int(original[counter1])
            counter1 += 1



    '''Substitute the boolean value of each literal into the formula'''
    def AssignValueFormula(self):
        newFormulaWithAssignment = self.formula

        for key in self.literalsValueComplement:
            newFormulaWithAssignment = newFormulaWithAssignment.replace(key,str(self.literalsValueComplement[key]))
        for key in self.literalsValue:
            newFormulaWithAssignment = newFormulaWithAssignment.replace(key,str(self.literalsValue[key]))

        #print(newFormulaWithAssignment)
        return newFormulaWithAssignment


    '''Check each of the clauses to get true or false value'''
    def CheckClauses(self,newFormula):
        stringLength = len(self.formula)
        newClauseFormula = ""
        
        for i in range (0,stringLength,14):
            if newFormula[i:i+11] != "":
                if i != 0:
                    newClauseFormula += " ∧ "
                if "1" in newFormula[i:i+11]:
                    newClauseFormula += "1"
                else:
                    newClauseFormula += "0"
                
        return newClauseFormula
                

    '''Check the entire formula to to determine whether a solution is found'''
    def CheckProblem(self,clauseFormula):
        if "0" in clauseFormula:
            return 0
        else:
            return 1

        


        
       
if __name__ == '__main__':
    _input=15
    a = SAT()
    counter = 0
    start = time.time()
    
    a.LiteralListGenerator(_input)
    a.DictKeyValueGenerator(_input)
    a.SetValueX(_input)
    '''print("Initialized literals list: ", a.literals,"\n")
    print("Initialized dictionary value:")
    print(a.literalsValue)
    print(a.literalsValueComplement)
    print()'''
    print("Problem Generation: " + a.ProblemGenerator(40) + "\n")

    print("Checking for solution...\n")
    while a.x != ("1"*_input):     
        if counter != 0:
            a.AssignValueDictionary()
            #print()
        else:
            '''print(a.literalsValue)
            print(a.literalsValueComplement)
            print()'''
            counter += 1
        b = a.CheckClauses(a.AssignValueFormula())
        '''print(b)
        print()'''
        c = a.CheckProblem(b)
        if c == 1:
            print("There is/are solution(s) for this 3-SAT problem.")
            '''print(a.literalsValue)
            print(a.literalsValueComplement)
            print(b)
            print(c)'''
            break
        if a.x == ("1"*_input) and c == 0:
            print("There is no solution for this 3-SAT problem.")

    end = time.time()
    print("\nTotal Computing time: ",end-start,"s")

