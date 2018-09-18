#include <iostream>
#include <string>
#include <vector>
#include <exception>
#include <sstream>
#include <memory>
#include <chrono>
#include <thread>
#include <fstream>
#include "prover.h"
using namespace std;
class UnificationTerm;
 bool alnum(string s) {
    if(s.length() == 0) return false;
    for(int i=0; i<s.length();i++) {
        if(!isalnum(s[i])) return false;
    }
    return true;
}
class Variable : public Container {
    string name;
    double time;
public:
    Variable(string namep, int timep) : Container("variable") {
        name = namep;
        time = timep;
    }
    shared_ptr<Container> replace(shared_ptr<Container> old, shared_ptr<Container> neww) {
        if(this->equates(old)) return neww;
        return shared_ptr<Container>(this);
    }
    vector<shared_ptr<Container> > freeVariables() { return vector<shared_ptr<Container>> {shared_ptr<Container>(this)};}
    vector<shared_ptr<Container> > freeUnificationTerms(){return vector<shared_ptr<Container >>{};}
    string getName() {return name;}
    void setInstantiationTime( double timep) {this->time = timep;}
    bool occurs(shared_ptr<Container> unification_term) {return false;}
    bool equates( shared_ptr<Container> other) {
         return ( name == other->getName() && other->getCName() == "variable");
    }
    string getCName() {return "variable";}
    vector<shared_ptr<Container>> getTerms() {return vector<shared_ptr<Container> >{};}
    shared_ptr<Container> getFormula() { return nullptr;}
    shared_ptr<Container> getFormulaA() { return nullptr;}
    shared_ptr<Container> getFormulaB() { return nullptr;}
    shared_ptr<Container> getVariable() { return nullptr;}
    int getTime() {return time;}
};
class UnificationTerm : public Container {
    double time;
    string name;
public:
     shared_ptr<Container> replace(shared_ptr<Container> old,shared_ptr<Container> neww) {
        if(this->equates(old)) return neww;
        return shared_ptr<Container>(this);
    }
    bool equates( shared_ptr<Container> other) {
        return (this->c_name == "unificationterm" && name == other->getName() && other->getCName() == "unificationterm");
    }
    vector<shared_ptr<Container> > freeVariables() {return vector<shared_ptr<Container>>{};}
    vector<shared_ptr<Container> > freeUnificationTerms(){return vector<shared_ptr<Container >>{shared_ptr<Container>(this)};}
    UnificationTerm(string namep) : Container("unificationterm") {name = namep;}
    string getName() {return name;}
    vector<shared_ptr<Container>> getTerms() {return vector<shared_ptr<Container>>{};}
    bool occurs( shared_ptr<Container> unification_term) {return this->equates(unification_term);} // mozda .name
    void setInstantiationTime(double timep) {this->time = timep;}
    string getCName() {return this->c_name;}
    shared_ptr<Container> getFormula() { return nullptr;}
    shared_ptr<Container> getFormulaA() { return nullptr;}
    shared_ptr<Container> getFormulaB() { return nullptr;}
    shared_ptr<Container> getVariable() { return nullptr;}
    int getTime() {return time;}
};
class Function : public Container {
    string name;
    double time;
    vector<shared_ptr<Container>> terms;
public:
     shared_ptr<Container> replace(shared_ptr<Container> old, shared_ptr<Container> neww) {
        if(this->equates(old)) return neww;
        vector<shared_ptr<Container>> term;
        for(int i=0;i<terms.size();i++) {
            term.push_back(terms[i]->replace(old,neww));
        }
        return make_shared<Function>( name,term);
    }
   bool equates( shared_ptr<Container> other) {
         bool jednako = true;
        if(other->getCName() != "function" || other->getName() != this->getName()  || this->getTerms().size() != other->getTerms().size()){
            return false;
        }
        for(int i=0; i< terms.size(); i++) {
            if(!(terms[i]->equates(other->getTerms()[i]))){
            return false;
            }
        }
        return true;
    }
    void setInstantiationTime(double timep){
        time = timep;
        for(int i=0; i<terms.size(); i++) {
            terms[i] -> setInstantiationTime(timep);
        }
    }
    string getName() {
        if (terms.size() == 0) return name;
        string full_name = name + "(";
        for (int i=0;i<terms.size(); i++) {
            full_name = full_name +  terms[i]->getName() ;
            if(i != terms.size()-1) full_name = full_name + ", ";
        }
        full_name = full_name + ")";
        return full_name;
    }
    vector<shared_ptr<Container>> getTerms() { return terms;}
    string getCName() {return "function";}
    Function(string namep, vector<shared_ptr<Container>> termsp) : Container("function") { name = namep; terms= termsp;}
     vector<shared_ptr<Container>> freeVariables() {
         if (terms.size()==0) return vector<shared_ptr<Container>>{};
         vector<shared_ptr<Container>> temp;
         for (int i=0;i<terms.size();i++) {
             vector<shared_ptr<Container>> temp2 = terms[i]->freeVariables();
             for(int j=0; j<temp2.size();j++) {
                temp.push_back(temp2[j]);
             }
         }
         return temp;
    }
    vector<shared_ptr<Container>> freeUnificationTerms(){
     if (terms.size()==0) return vector<shared_ptr<Container >>{};
         vector<shared_ptr<Container>> temp;
         for (int i=0;i<terms.size();i++) {
             vector<shared_ptr<Container>> temp2 = terms[i]->freeUnificationTerms();
             for(int j=0; j<temp2.size();j++) {
                temp.push_back(temp2[j]);
             }
         }
         return temp;
    }
    bool occurs( shared_ptr<Container> unification_term) {
        for ( int i=0; i<terms.size(); i++ ) {
            if((terms[i]->equates(unification_term)) ) {
                return true;
            }
        }
        return false;
    }
    shared_ptr<Container> getFormula() { return nullptr;}
    shared_ptr<Container> getFormulaA() { return nullptr;}
    shared_ptr<Container> getFormulaB() { return nullptr;}
    shared_ptr<Container> getVariable() { return nullptr;}
    int getTime() {return time;}
};
//Formulae
class Predicate : public Container {
    string name;
    vector<shared_ptr<Container >> terms;
public:
    shared_ptr<Container> replace(shared_ptr<Container> old, shared_ptr<Container> neww) {
        if(this->equates(old)) return neww;
        vector<shared_ptr<Container>> term;
        for(int i=0;i<terms.size();i++) {
            term.push_back(terms[i]->replace(old,neww));
        }
        return make_shared<Predicate>(name,term);
    }
    bool equates( shared_ptr<Container> other) {
        if(other->getCName() != "predicate" || other->getName() != this->getName()  || this->getTerms().size() != other->getTerms().size()){
            return false;
        }
        for(int i=0; i< terms.size(); i++) {
            if(!(terms[i]->equates(other->getTerms()[i]))){
            return false;
            }
        }
        return true;
    }
    Predicate(string namep, vector<shared_ptr<Container>> termsp) : Container("predicate") {name = namep; terms=termsp;}
    vector<shared_ptr<Container>> freeVariables() {
         if (terms.size()==0) return vector<shared_ptr<Container>>{};
         vector<shared_ptr<Container>> temp;
         for (int i=0;i<terms.size();i++) {
             vector<shared_ptr<Container>> temp2 = terms[i]->freeVariables();
             for(int j=0; j<temp2.size();j++) {
                temp.push_back(temp2[j]);
             }
         }
         return temp;
    }
    vector<shared_ptr<Container >> freeUnificationTerms(){
     if (terms.size()==0) return vector<shared_ptr<Container>>{};
         vector<shared_ptr<Container>> temp;
         for (int i=0;i<terms.size();i++) {
             vector<shared_ptr<Container>> temp2 = terms[i]->freeUnificationTerms();
             for(int j=0; j<temp2.size();j++) {
                temp.push_back(temp2[j]);
             }
         }
         return temp;
    }
    vector<shared_ptr<Container>> getTerms() { return terms;}
    string getCName() {return this->c_name;}
    bool occurs( shared_ptr<Container> unification_term) {
        for ( int i=0; i<terms.size(); i++ ) {
            if((terms[i]->equates(unification_term) )) {
                return true;
            }
        }
        return false;
    }
    void setInstantiationTime(double timep){
        for(int i=0; i<terms.size(); i++) {
            terms[i] -> setInstantiationTime(timep);
        }
    }
     string getName() {
        if (terms.size() == 0) return name;
        string full_name = name + "(";
        for (int i=0;i<terms.size(); i++) {
            full_name = full_name +  terms[i]->getName();
            if(i != terms.size()-1) full_name = full_name + ", ";
        }
        full_name = full_name + ")";
        return full_name;
    }
     shared_ptr<Container> getFormula()  { return nullptr;}
     shared_ptr<Container> getFormulaA() { return nullptr;}
     shared_ptr<Container> getFormulaB() { return nullptr;}
     shared_ptr<Container> getVariable() { return nullptr;}
     int getTime() {return 0;}
};
class Necessarily : public Container {
    shared_ptr<Container> formula;
public:
    shared_ptr<Container> replace(shared_ptr<Container> old, shared_ptr<Container> neww) {
        if(this->equates(old)) return neww;
        return make_shared<Necessarily>(formula->replace(old,neww));
    }
    bool equates( shared_ptr<Container> other)  {
        if(other->getCName()!="necessarily") return false;
        return (formula->equates(other->getFormula()));
    }
    Necessarily(shared_ptr<Container> formulap) : Container("necessarily") {formula = formulap;}
    vector<shared_ptr<Container>> freeVariables() {return formula->freeVariables();}
    vector<shared_ptr<Container>> freeUnificationTerms(){return formula->freeUnificationTerms();}
    bool occurs( shared_ptr<Container> unification_term) {
        return this->formula->occurs(unification_term);
    }
    void setInstantiationTime(double timep){
        this->formula->setInstantiationTime(timep);
    }
    shared_ptr<Container> getFormula() { return formula;}
    shared_ptr<Container> getFormulaA() { return nullptr;}
    shared_ptr<Container> getFormulaB() { return nullptr;}
    shared_ptr<Container> getVariable() { return nullptr;}
    string getName() {
        string s= "necessarily ";
        string s2 = "(";
        string s3 = s + s2 + formula->getName() + ") ";
        return s3;
    }
    string getCName() {return "necessarily";}
    vector<shared_ptr<Container >> getTerms() {return vector<shared_ptr<Container >>{};}
    int getTime() {return 0;}
};
class Possibly : public Container {
    shared_ptr<Container> formula;
public:
    shared_ptr<Container> replace(shared_ptr<Container> old, shared_ptr<Container> neww) {
        if(this->equates(old)) return neww;
        return make_shared<Possibly>(formula->replace(old,neww));
    }
   bool equates( shared_ptr<Container> other)  {
        if(other->getCName()!="possibly") return false;
        return (formula->equates(other->getFormula()));
    }
    Possibly(shared_ptr<Container> formulap) : Container("possibly") {formula = formulap;}
    vector<shared_ptr<Container >> freeVariables() {return formula->freeVariables();}
    vector<shared_ptr<Container>> freeUnificationTerms(){return formula->freeUnificationTerms();}
    bool occurs( shared_ptr<Container> unification_term) {
        return this->formula->occurs(unification_term);
    }
    void setInstantiationTime(double timep){
        this->formula->setInstantiationTime(timep);
    }
    shared_ptr<Container> getFormula() { return formula;}
    shared_ptr<Container> getFormulaA() { return nullptr;}
    shared_ptr<Container> getFormulaB() { return nullptr;}
    shared_ptr<Container> getVariable() { return nullptr;}
    string getName() {
        return string("possibly ") + string("(") + formula->getName() + ") ";
    }
    string getCName() {return "possibly";}
    vector<shared_ptr<Container>> getTerms() {return vector<shared_ptr<Container>>{};}
    int getTime() {return 0;}
};
class Not : public Container {
    shared_ptr<Container> formula;
public:
    shared_ptr<Container> replace(shared_ptr<Container> old,shared_ptr<Container> neww) {
        if(this->equates(old)) return neww;
        return make_shared<Not>(formula->replace(old,neww));
    }
    bool equates( shared_ptr<Container> other)  {
    if(other->getCName()!="not") return false;
        return (formula->equates(other->getFormula()));
    }
    Not(shared_ptr<Container> formulap) : Container("not") {formula = formulap;}
    vector<shared_ptr<Container>> freeVariables() {return formula->freeVariables();}
    vector<shared_ptr<Container >> freeUnificationTerms(){return formula->freeUnificationTerms();}
    bool occurs( shared_ptr<Container> unification_term) {
        return this->formula->occurs(unification_term);
    }
    void setInstantiationTime(double timep){
        this->formula->setInstantiationTime(timep);
    }
    shared_ptr<Container> getFormula() { return formula;}
    shared_ptr<Container> getFormulaA() { return nullptr;}
    shared_ptr<Container> getFormulaB() { return nullptr;}
    shared_ptr<Container> getVariable() { return nullptr;}
    string getName() {
        return string("not ") + "(" + formula->getName() + ") ";
    }
    string getCName() {return "not";}
    vector<shared_ptr<Container >> getTerms() {return vector<shared_ptr<Container>>{};}
    int getTime() {return 0;}
};
class And: public Container {
    shared_ptr<Container > formula_a;
    shared_ptr<Container> formula_b;
public:
     shared_ptr<Container> replace(shared_ptr<Container> old, shared_ptr<Container> neww) {
        if(this->equates(old)) return neww;
        return  make_shared<And>(formula_a->replace(old,neww), formula_b->replace(old,neww));
    }
   bool equates( shared_ptr<Container> other) {
        if(other->getCName()!="and") return false;
        return ((formula_a->equates(other->getFormulaA())) && (formula_b->equates(other->getFormulaB())));
    }
    And(shared_ptr<Container> formula_ap, shared_ptr<Container> formula_bp) : Container("and") {formula_a = formula_ap; formula_b=formula_bp; }
    vector<shared_ptr<Container>> freeVariables() {
        vector<shared_ptr<Container>> temp1 = formula_a->freeVariables();
        vector<shared_ptr<Container >> temp2 = formula_b->freeVariables();
        temp1.insert(temp1.end(),temp2.begin(),temp2.end());
        return temp1;
    }
    vector<shared_ptr<Container >> freeUnificationTerms(){
        vector<shared_ptr<Container>> temp1 = formula_a->freeUnificationTerms();
        vector<shared_ptr<Container>> temp2 = formula_b->freeUnificationTerms();
        temp1.insert(temp1.end(),temp2.begin(),temp2.end());
        return temp1;
    }
    bool occurs( shared_ptr<Container> unification_term) {
        return (this->formula_a->occurs(unification_term) || this->formula_b->occurs(unification_term));
    }
    void setInstantiationTime(double timep){
        this->formula_a->setInstantiationTime(timep);
        this->formula_b->setInstantiationTime(timep);
    }
    shared_ptr<Container> getFormula()  { return nullptr;}
    shared_ptr<Container> getFormulaA() { return formula_a;}
    shared_ptr<Container> getFormulaB() { return formula_b;}
    shared_ptr<Container> getVariable() { return nullptr;}
    string getName() {
        return " (" + formula_a->getName() + ") " "and " + "(" + formula_b->getName() +") ";
    }
    string getCName() {return "and";}
    vector<shared_ptr<Container>> getTerms() {return vector<shared_ptr<Container>>{};}
    int getTime() {return 0;}
};
class Or: public Container {
    shared_ptr<Container> formula_a;
    shared_ptr<Container> formula_b;
public:
    shared_ptr<Container> replace(shared_ptr<Container> old, shared_ptr<Container> neww) {
        if(this->equates(old)) return neww;
        return make_shared<Or>(formula_a->replace(old,neww), formula_b->replace(old,neww));
    }
    bool equates( shared_ptr<Container> other) {
        if(other->getCName()!="or") return false;
        return ((formula_a->equates(other->getFormulaA())) && (formula_b->equates(other->getFormulaB())));
    }
    Or(shared_ptr<Container> formula_ap, shared_ptr<Container> formula_bp) : Container("or") {formula_a = formula_ap; formula_b=formula_bp; }
    vector<shared_ptr<Container>> freeVariables() {
        vector<shared_ptr<Container>> temp1 = formula_a->freeVariables();
        vector<shared_ptr<Container>> temp2 = formula_b->freeVariables();
        temp1.insert(temp1.end(),temp2.begin(),temp2.end());
        return temp1;
    }
    vector<shared_ptr<Container>> freeUnificationTerms(){
        vector<shared_ptr<Container>> temp1 = formula_a->freeUnificationTerms();
        vector<shared_ptr<Container>> temp2 = formula_b->freeUnificationTerms();
        temp1.insert(temp1.end(),temp2.begin(),temp2.end());
        return temp1;
    }
    bool occurs( shared_ptr<Container> unification_term) {
        return (this->formula_a->occurs(unification_term) || this->formula_b->occurs(unification_term));
    }
    void setInstantiationTime(double timep){
        this->formula_a->setInstantiationTime(timep);
        this->formula_b->setInstantiationTime(timep);
    }
    shared_ptr<Container> getFormula() { return nullptr;}
    shared_ptr<Container> getFormulaA() { return formula_a;}
    shared_ptr<Container> getFormulaB() { return formula_b;}
    shared_ptr<Container> getVariable() { return nullptr;}
    string getName() {
        return " (" + formula_a->getName() + ") " + "or " + "(" + formula_b->getName() + ") ";
    }
    string getCName() {return "or";}
    vector<shared_ptr<Container>> getTerms() {return vector<shared_ptr<Container>>{};}
    int getTime() {return 0;}
};
class Implies: public Container {
    shared_ptr<Container> formula_a;
    shared_ptr<Container> formula_b;
public:
     shared_ptr<Container> replace(shared_ptr<Container> old, shared_ptr<Container> neww) {
        if(this->equates(old)) return neww;
        return make_shared<Implies>(formula_a->replace(old,neww), formula_b->replace(old,neww));
    }
    bool equates( shared_ptr<Container> other) {
         if(other->getCName()!="implies") return false;
        return ((formula_a->equates(other->getFormulaA())) && (formula_b->equates(other->getFormulaB())));
    }
    Implies(shared_ptr<Container> formula_ap, shared_ptr<Container> formula_bp) : Container("implies") {formula_a = formula_ap; formula_b=formula_bp; }
    vector<shared_ptr<Container >> freeVariables() {
        vector<shared_ptr<Container>> temp1 = formula_a->freeVariables();
        vector<shared_ptr<Container>> temp2 = formula_b->freeVariables();
        temp1.insert(temp1.end(),temp2.begin(),temp2.end());
        return temp1;
    }
    vector<shared_ptr<Container>> freeUnificationTerms(){
        vector<shared_ptr<Container>> temp1 = formula_a->freeUnificationTerms();
        vector<shared_ptr<Container>> temp2 = formula_b->freeUnificationTerms();
        temp1.insert(temp1.end(),temp2.begin(),temp2.end());
        return temp1;
    }
    bool occurs( shared_ptr<Container> unification_term) {
        return (this->formula_a->occurs(unification_term) || this->formula_b->occurs(unification_term));
    }
     void setInstantiationTime(double timep){
        this->formula_a->setInstantiationTime(timep);
        this->formula_b->setInstantiationTime(timep);
    }
    shared_ptr<Container> getFormula() { return nullptr;}
    shared_ptr<Container> getFormulaA() { return formula_a;}
    shared_ptr<Container> getFormulaB() { return formula_b;}
    shared_ptr<Container> getVariable() { return nullptr;}
    string getName() {
        return " (" + formula_a->getName() + ")" + " implies " + "(" + formula_b->getName() + ") ";
    }
    string getCName() {return "implies";}
    vector<shared_ptr<Container>> getTerms() {return vector<shared_ptr<Container >>{};}
    int getTime() {return 0;}
};
class ForAll: public Container {
    shared_ptr<Container> formula;
    shared_ptr<Container> variable;
public:
     shared_ptr<Container> replace(shared_ptr<Container> old, shared_ptr<Container> neww) {
        if(this->equates(old)) return neww;
        return make_shared<ForAll>(formula->replace(old,neww), variable->replace(old,neww));
    }
    bool equates( shared_ptr<Container> other) {
        if(other->getCName()!="forall") return false;
        return ((formula->equates(other->getFormula())) && (variable->equates(other->getVariable())));
    }
    ForAll(shared_ptr<Container> formulap, shared_ptr<Container> variablep) : Container("forall") {formula = formulap; variable=variablep; }
    vector<shared_ptr<Container>> freeVariables() { ///////????????
        vector<shared_ptr<Container>> temp = formula->freeVariables();
        for(int i=0; i<temp.size();i++) {
            if(temp[i]->equates(variable)) {
                temp.erase(temp.begin()+1);
                break;
            }
        }
        return temp;
    }
    int getTime() {return 0;}
    vector<shared_ptr<Container>> freeUnificationTerms(){ return formula->freeUnificationTerms();}
    bool occurs(shared_ptr<Container> unification_term) {
        return (this->formula->occurs(unification_term) );
    }
     void setInstantiationTime(double timep){
        this->formula->setInstantiationTime(timep);
        this->variable->setInstantiationTime(timep);
    }
    shared_ptr<Container> getFormula() { return formula;}
    shared_ptr<Container> getVariable() { return variable;}
    shared_ptr<Container> getFormulaA() { return nullptr;}
    shared_ptr<Container> getFormulaB() { return nullptr;}
    string getName() {
        return " for all " + variable->getName() + ". " + formula->getName();
    }
    string getCName() {return "forall";}
    vector<shared_ptr<Container>> getTerms() {return vector<shared_ptr<Container>>{};}
};
class ThereExists: public Container {
    shared_ptr<Container> formula;
    shared_ptr<Container> variable;
public:
    shared_ptr<Container> replace(shared_ptr<Container> old, shared_ptr<Container> neww) {
        if(this->equates(old)) return neww;
        return make_shared<ThereExists>(formula->replace(old,neww), variable->replace(old,neww));
    }
    bool equates( shared_ptr<Container> other) {
        if(other->getCName()!="thereexists") return false;
        return ((formula->equates(other->getFormula())) && (variable->equates(other->getVariable())));
    }
    ThereExists(shared_ptr<Container> formulap, shared_ptr<Container> variablep) : Container("thereexists") {formula = formulap; variable=variablep; }
     vector<shared_ptr<Container> > freeVariables() {
        vector<shared_ptr<Container >> temp = formula->freeVariables();
        for(int i=0; i<temp.size();i++) {
            if(temp[i]->equates(variable)) {
                temp.erase(temp.begin()+1);
                break;
            }
        }
        return temp;
    }
    vector<shared_ptr<Container>> freeUnificationTerms(){ return formula->freeUnificationTerms();}
    int getTime() {return 0;}
    bool occurs( shared_ptr<Container> unification_term) {
        return (this->formula->occurs(unification_term) );
    }
    void setInstantiationTime(double timep){
        this->formula->setInstantiationTime(timep);
        this->variable->setInstantiationTime(timep);
    }
    shared_ptr<Container> getFormula() { return formula;}
    shared_ptr<Container> getVariable() { return variable;}
    shared_ptr<Container> getFormulaA() { return nullptr;}
    shared_ptr<Container> getFormulaB() { return nullptr;}
    string getName() {
        return " exists " + variable->getName() + ". " + formula->getName();
    }
    string getCName() { return "thereexists";}
    vector<shared_ptr<Container >> getTerms() {return vector<shared_ptr<Container>>{};}
};

shared_ptr<Container> parse(vector<string> tokens) {
    vector<string> keywords = {"not","implies","and","or","forall","exists","necessarily","possibly"};
    if (tokens.size()== 0) throw string("Empty formula");
    //ForAll
    if (tokens[0] == "forall") {
        int dot_pos = -1;
        for (int i=1;i<tokens.size();i++) {
            if (tokens[i]== ".") {
                dot_pos = i;
                break;
            }
        }
        if (dot_pos == -1) throw string("Missing . in forallquantifier");
        vector<shared_ptr<Container >> args;
        int i=1;
        int end;
        while (i<=dot_pos) {
            end = dot_pos;
            int depth = 0;
            for (int j=i; j<dot_pos; j++) {
                if (tokens[j]=="(") {
                    depth += 1;
                    continue;
                }
                if (tokens[j]==")") {
                    depth -=1;
                    continue;
                }
                if(depth == 0 && tokens[j]==",") {
                    end = j;
                    break;
                }
            }
            if (i==end) throw string("Missing variable in forall quantifier");
            vector<string> temp;
            for(int j=i;j<end;j++) temp.push_back(tokens[j]);
            args.push_back(parse(temp));
            i=end+1;
        }
        if(tokens.size() == (dot_pos+1)) throw string("Missing formula in forall quantifier");
        vector<string> temp2;
        for(int k=dot_pos+1;k<tokens.size();k++) temp2.push_back(tokens[k]);
        shared_ptr<Container> formula = parse(temp2);
        for (int k=args.size()-1;k>=0;k--) {
            formula = make_shared<ForAll>(formula,args[k]);
        }
        return formula;
    }
    //ThereExists
    if (tokens[0] =="exists") {
        int dot_pos = -1;
        for (int i=1; i<tokens.size();i++) {
            if(tokens[i]== "."){
                dot_pos = i;
                break;
            }
        }
        if (dot_pos == -1) throw string("Missing . in exists quantifier");
        if (dot_pos == 1) throw string("Missing variable in exists quantifier");
        vector<shared_ptr<Container>> args;
        int i=1;
        int end;
        int depth;
        while (i<=dot_pos) {
            end = dot_pos;
            depth = 0;
            for (int j=i; j<dot_pos; j++) {
                if(tokens[j]=="(") {
                    depth +=1;
                    continue;
                }
                if(tokens[j]==")") {
                    depth -= 1;
                    continue;
                }
                if(depth == 0 and tokens[j]==","){
                    end = j;
                    break;
                }
            }
            if (i==end) throw string("Missing variable in exists quantifier");
            vector<string> temp;
            for(int k=i;k<end;k++) temp.push_back(tokens[k]);
            args.push_back(parse(temp));
            i=end +1;
        }
        if(tokens.size()==dot_pos+1) throw string("Missing formula in exists quantifier");
        vector<string> temp2;
        for(int k=dot_pos+1;k<tokens.size();k++) temp2.push_back(tokens[k]);
        shared_ptr<Container> formula = parse(temp2);
        for(int k=args.size()-1; k>=0;k--) {
            formula = make_shared<ThereExists>(formula,args[k]);
        }
        return formula;
    }
    //Imolies
    int implies_pos = -1;
    int depth = 0;
    for (int i=0; i<tokens.size();i++) {
        if(tokens[i]=="(") {
            depth+=1;
            continue;
        }
        if(tokens[i]==")") {
            depth -=1;
            continue;
        }
        if(depth==0 && tokens[i]=="implies") {
            implies_pos=i;
            break;
        }
    }
    if(implies_pos != -1) {
        bool quantifier_in_left = false;
        depth = 0;
        for (int i=0; i<implies_pos; i++) {
            if(tokens[i]=="(") {
                depth +=1;
                continue;
            }
            if(tokens[i]==")") {
                depth -=1;
                continue;
            }
            if(depth==0 && (tokens[i]=="forall" || tokens[i]=="exists")) {
                quantifier_in_left = true;
                break;
            }
        }
        if (!quantifier_in_left) {
            if(implies_pos==0 || implies_pos==tokens.size()-1) throw string("Missing formula in implies connective");
            vector<string> temp;
            for(int k=0;k<implies_pos;k++) temp.push_back(tokens[k]);
            vector<string> temp2;
            for(int k=implies_pos+1;k<tokens.size();k++) temp2.push_back(tokens[k]);
            return make_shared<Implies>(parse(temp),parse(temp2));
        }
    }
    //Or
    int or_pos = -1;
    depth = 0;
    for (int i=0; i<tokens.size();i++) {
        if(tokens[i]=="(") {
            depth+=1;
            continue;
        }
        if(tokens[i]==")") {
            depth -=1;
            continue;
        }
        if(depth==0 && tokens[i]=="or") {
            or_pos=i;
            break;
        }
    }
    if(or_pos != -1) {
        bool quantifier_in_left = false;
        depth = 0;
        for (int i=0; i<or_pos; i++) {
            if(tokens[i]=="(") {
                depth +=1;
                continue;
            }
            if(tokens[i]==")") {
                depth -=1;
                continue;
            }
            if(depth==0 && (tokens[i]=="forall" || tokens[i]=="exists")) {
                quantifier_in_left = true;
                break;
            }
        }
        if (!quantifier_in_left) {
            if(or_pos==0 || or_pos==tokens.size()-1) throw string("Missing formula in or connective");
            vector<string> temp;
            for(int k=0;k<or_pos;k++) temp.push_back(tokens[k]);
            vector<string> temp2;
            for(int k=or_pos+1;k<tokens.size();k++) temp2.push_back(tokens[k]);
            return shared_ptr<Container>(new Or(parse(temp),parse(temp2)));
        }
    }
    //And
    int and_pos = -1;
     depth = 0;
    for (int i=0; i<tokens.size();i++) {
        if(tokens[i]=="(") {
            depth+=1;
            continue;
        }
        if(tokens[i]==")") {
            depth -=1;
            continue;
        }
        if(depth==0 and tokens[i]=="and") {
            and_pos=i;
            break;
        }
    }
    if(and_pos != -1) {
        bool quantifier_in_left = false;
        depth = 0;
        for (int i=0; i<and_pos; i++) {
            if(tokens[i]=="(") {
                depth +=1;
                continue;
            }
            if(tokens[i]==")") {
                depth -=1;
                continue;
            }
            if(depth==0 && (tokens[i]=="forall" || tokens[i]=="exists")) {
                quantifier_in_left = true;
                break;
            }
        }
        if (!quantifier_in_left) {
            if(and_pos==0 || and_pos==tokens.size()-1) throw string("Missing formula in and connective");
            vector<string> temp;
            for(int k=0;k<and_pos;k++) temp.push_back(tokens[k]);
            vector<string> temp2;
            for(int k=and_pos+1;k<tokens.size();k++) temp2.push_back(tokens[k]);
            return make_shared<And>(parse(temp),parse(temp2));
        }
    }
    //Not
    if(tokens[0]=="not") {
        if (tokens.size()<2) throw string("Missing formula is NOT connective");
        vector<string> temp;
        for(int k=1;k<tokens.size();k++) temp.push_back(tokens[k]);
        return make_shared<Not>(parse(temp));
    }
    //Neccesarily
    if(tokens[0]== "necessarily") {
        if (tokens.size()<2) throw string("Missing formula is neccesarily connective");
        vector<string> temp;
        for(int k=1;k<tokens.size();k++) temp.push_back(tokens[k]);
        return make_shared<Necessarily>(parse(temp));
    }
    //Neccesarily
    if(tokens[0]== "possibly") {
        if (tokens.size()<2) throw string("Missing formula is possibly connective");
        vector<string> temp;
        for(int k=1;k<tokens.size();k++) temp.push_back(tokens[k]);
        return make_shared<Possibly>(parse(temp));
    }
    //Function
    bool in_keywords = false;
    for(int i=0; i<keywords.size();i++) if(tokens[0]==keywords[i]) {in_keywords = true; break;}
    if(alnum(tokens[0]) && !in_keywords && tokens.size() > 1 && tokens[1]=="(" ) {
        if(tokens[tokens.size()-1] != ")") throw string("Missing ) after function argument list");
        string name = tokens[0];
        vector<shared_ptr<Container>> args;
        int i=2;
        int end;
        if(i<tokens.size()-1) {
            while (i<=tokens.size()-1) {
                 end = tokens.size()-1;
                 depth = 0;
                 for (int j=i;j<tokens.size()-1; j++) {
                    if(tokens[j]=="(") {
                        depth +=1;
                        continue;
                    }
                    if(tokens[j]==")") {
                        depth -=1;
                        continue;
                    }
                    if(depth==0 && tokens[j]==","){
                        end =j;
                        break;
                    }
                 }
                 if(i==end) throw string("Missing function argument");
                 vector<string> temp;
                 for(int k=i;k<end;k++) temp.push_back(tokens[k]);
                 args.push_back(parse(temp));
                 i=end+1;
            }
        }
        return make_shared<Function>(name,args);
    }
    //Predicate
      in_keywords = false;
    for(int i=0; i<keywords.size();i++) if(tokens[0]==keywords[i]) {in_keywords = true; break;}
    if(alnum(tokens[0]) && !in_keywords && tokens.size() == 1 ) {
            return make_shared<Predicate>(tokens[0],vector<shared_ptr<Container>>{});
    }
    if(alnum(tokens[0]) && !in_keywords && tokens.size() >1 && tokens[1]=="(" ) {
        if(tokens[tokens.size()-1] != ")") throw string("Missing ) after predicate argument list");
        string name = tokens[0];
        vector<shared_ptr<Container>> args;
        int i=2;
        int end;
        if(i<tokens.size()-1) {
            while (i<=tokens.size()-1) {
                 end = tokens.size()-1;
                 depth = 0;
                 for (int j=i;j<tokens.size()-1; j++) {
                    if(tokens[j]=="(") {
                        depth +=1;
                        continue;
                    }
                    if(tokens[j]==")") {
                        depth -=1;
                        continue;
                    }
                    if(depth==0 && tokens[j]==","){
                        end =j;
                        break;
                    }
                 }
                 if(i==end) throw string("Missing predicate argument");
                 vector<string> temp;
                 for(int k=i;k<end;k++) temp.push_back(tokens[k]);
                 args.push_back(parse(temp));
                 i=end+1;
            }
        }
        return make_shared<Predicate>(name,args);
    }
    //Variable
      in_keywords = false;
    for(int i=0; i<keywords.size();i++) if(tokens[0]==keywords[i]) {in_keywords = true; break;}
    if(alnum(tokens[0]) && !in_keywords && tokens.size() == 1 ) {
            return make_shared<Variable>(tokens[0],0);
    }
    //Group
    if(tokens[0]=="(") {
        if(tokens[tokens.size()-1] != ")") throw string("Missing )");
        if(tokens.size()==2) throw string("Missing formula in parenthetical group");
        vector<string> temp;
        for(int k=1;k<tokens.size()-1;k++) temp.push_back(tokens[k]);
        return parse(temp);
    }

    throw string ("Unable to parse");
}
//unify
pair<vector<pair<shared_ptr<Container>,shared_ptr<Container>>>,bool> unify(shared_ptr<Container> term_a, shared_ptr<Container> term_b) {

    if (term_a->getCName() == "unificationterm") {
        if (term_b->occurs(term_a) || term_b->getTime() > term_a->getTime()) {
            return make_pair(vector<pair<shared_ptr<Container>,shared_ptr<Container >>> {},false);
        }
        return make_pair(vector<pair<shared_ptr<Container>,shared_ptr<Container >>> {make_pair(term_a, term_b)},true);
    }
    if(term_b->getCName() == "unificationterm") {
        if (term_a->occurs(term_a) || term_a->getTime() > term_b->getTime()) {
            return make_pair(vector<pair<shared_ptr<Container>,shared_ptr<Container>>> {},false);
        }
        return make_pair(vector<pair<shared_ptr<Container>,shared_ptr<Container>>> {make_pair(term_b, term_a)},true);
    }
    if(term_a->getCName() == "variable" && term_b->getCName() == "variable") {
        if(term_a->equates(term_b)) { //***
            return make_pair(vector<pair<shared_ptr<Container >,shared_ptr<Container >>> {},true);
        }
        return make_pair(vector<pair<shared_ptr<Container>,shared_ptr<Container >>> {},false);
    }
    if((term_a->getCName() == "function" && term_b->getCName() == "function" )
       || (term_a->getCName() == "predicate" && term_b->getCName() == "predicate") ){

        if(term_a->getTerms().size() != term_b->getTerms().size()) {
            return make_pair(vector<pair<shared_ptr<Container >,shared_ptr<Container >>> {},false);
        }
        pair<vector<pair<shared_ptr<Container>,shared_ptr<Container >>>,bool> substitution= make_pair(vector<pair<shared_ptr<Container>,shared_ptr<Container>>>{},true);
        for(int i= 0; i<term_a->getTerms().size(); i++) {
            shared_ptr<Container> a = term_a->getTerms()[i];
            shared_ptr<Container> b = term_b->getTerms()[i];
            for(int j=0; j<substitution.first.size();j++) {
                a = a->replace(substitution.first[j].first,substitution.first[j].second);
                b = b->replace(substitution.first[j].first,substitution.first[j].second);
            }
            pair<vector<pair<shared_ptr<Container>,shared_ptr<Container >>>,bool> sub = unify(a,b);
            if (sub.second == false) {
                return make_pair(vector<pair<shared_ptr<Container>,shared_ptr<Container>>> {},false);
            }
            for(int j=0;j<sub.first.size();j++) {
                substitution.first.push_back(make_pair(sub.first[j].first,sub.first[j].second));
            }
        }
        return substitution;
        }
        return make_pair(vector<pair<shared_ptr<Container >,shared_ptr<Container>>> {},false);
}
//perform unification for a list
pair<vector<pair<shared_ptr<Container>,shared_ptr<Container >>>,bool> unify_list(vector<pair<shared_ptr<Container>, shared_ptr<Container >>> pairs) {
    pair<vector<pair<shared_ptr<Container>,shared_ptr<Container>>>,bool> substitution = make_pair(vector<pair<shared_ptr<Container>,shared_ptr<Container>>>{},true);
    for(int i=0; i<pairs.size();i++) {
        shared_ptr<Container> a = pairs[i].first;
        shared_ptr<Container> b = pairs[i].second;
        for(int j=0; j<substitution.first.size(); j++) {
            a = a->replace(substitution.first[j].first,substitution.first[j].second);
            b = b->replace(substitution.first[j].first,substitution.first[j].second);
        }
        pair<vector<pair<shared_ptr<Container>,shared_ptr<Container>>>,bool> sub = unify(a,b);
        if(sub.second == false) {
            return make_pair(vector<pair<shared_ptr<Container>,shared_ptr<Container >>> {},false);
        }
        for(int j=0;j<sub.first.size();j++) {
            substitution.first.push_back(make_pair(sub.first[j].first,sub.first[j].second));
        }
    }
    return substitution;
}
//definition of sequent
class Sequent {
    vector<pair<shared_ptr<Container>,int>> left;
    vector<pair<shared_ptr<Container>,int>> right;
    vector<shared_ptr<Sequent>> siblings;
    int i=0;
    int depth;
public:
    Sequent(vector<pair<shared_ptr<Container>,int>> leftp,vector<pair<shared_ptr<Container>,int>> rightp,vector<shared_ptr<Sequent> > siblingsp,int depthp ){
        left=leftp;
        right= rightp;
        siblings = siblingsp;
        depth = depthp;
    }
    void setLeftDepth(int pos_ind,int depthp) {
        left[pos_ind].second = depthp;
    }
    void setRightDepth(int pos_ind,int depthp) {
        right[pos_ind].second = depthp;
    }
    void eraseLeftAt(int i) {
       left.erase(left.begin()+i);
    }
    void eraseRightAt(int i) {
       right.erase(right.begin()+i);
    }
    void addRight(pair<shared_ptr<Container>,int> p) {
        bool there =false;
        for(int i=0;i<right.size();i++) {
            if(right[i].first->equates(p.first)) there = true;
        }
        if(!there) right.push_back(p);
    }
    void addLeft(pair<shared_ptr<Container>,int> p) {
        bool there =false;
        for(int i=0;i<left.size();i++) {
            if(left[i].first->equates(p.first)) there = true;
        }
        if(!there) left.push_back(p);
    }
    void addSibling(shared_ptr<Sequent> s) {
        siblings.push_back(s);
    }
    void removeSibling(shared_ptr<Sequent> s) {
       for(int i=0;i<siblings.size();i++) {
        if(s->equates(siblings[i])) {
            siblings.erase(siblings.begin()+i);
            i--;
        }
       }
    }
    vector<pair<shared_ptr<Container>,int>> getLeft(){return left;}
    vector<pair<shared_ptr<Container>,int>> getRight(){return right;}
    vector<shared_ptr<Sequent>> getSiblings(){return siblings;}
    int getDepth() {return depth;}
    string getVariableName(string prefix) {
        vector<shared_ptr<Container>> fv = this->freeVariables();
        vector<shared_ptr<Container>> fv2 = this->freeUnificationTerms();
        fv.insert(fv.end(),fv2.begin(),fv2.end());
        int index = 1;
        stringstream convert;
        convert << index;
        string name = prefix + convert.str();
        for(int i=0;i<fv.size(); i++) {
            if( fv[i]->equates(shared_ptr<Container>(new Variable(name,0))) || fv[i]->equates(shared_ptr<Container>(new UnificationTerm(name)))) {
                index += 1;
                 stringstream convert2;
                convert2 << index;
                name = prefix + convert2.str();
                i=-1;
            }
        }
        return name;
    }
    vector<shared_ptr<Container>> freeVariables() {
        vector<shared_ptr<Container>> temp;
        for (int i=0; i<left.size();i++) {
            vector<shared_ptr<Container>> temp2 = left[i].first->freeVariables();
            temp.insert(temp.begin(),temp2.begin(),temp2.end());
        }
        for (int i=0; i<right.size();i++) {
            vector<shared_ptr<Container >> temp2 = right[i].first->freeVariables();
            temp.insert(temp.begin(),temp2.begin(),temp2.end());
        }
       return temp;
    }
    vector<shared_ptr<Container>> freeUnificationTerms(){
        vector<shared_ptr<Container >> temp;
        for (int i=0; i<left.size();i++) {
            vector<shared_ptr<Container>> temp2 = left[i].first->freeUnificationTerms();
            temp.insert(temp.begin(),temp2.begin(),temp2.end());
        }
        for (int i=0; i<right.size();i++) {
            vector<shared_ptr<Container>> temp2 = right[i].first->freeUnificationTerms();
            temp.insert(temp.begin(),temp2.begin(),temp2.end());
        }
        return temp;
    }
    vector<pair<shared_ptr<Container>,shared_ptr<Container>>> getUnifiablePairs() {
        vector<pair<shared_ptr<Container>,shared_ptr<Container>>> pairs;
        for(int i=0;i<left.size();i++) {
            for(int j=0; j<right.size();j++) {
                if( unify(left[i].first,right[j].first).second == true) {

                    pairs.push_back(make_pair(left[i].first,right[j].first));
                }
            }
        }
        return pairs;
    }
    bool equates(shared_ptr<Sequent> other) {
        for(int i=0;i<left.size();i++) {
            bool in_left = false;
            for(int j=0;j<other->getLeft().size();j++) {
                if (left[i].first->equates(other->getLeft()[j].first)) {
                    in_left = true;
                    break;
                }
            }
            if(!in_left) return false;
        }
        for(int i=0;i<right.size();i++) {
            bool in_right = false;
            for(int j=0;j<other->getRight().size();j++) {
                if (right[i].first->equates(other->getRight()[j].first)) {
                    in_right = true;
                    break;
                }
            }
            if(!in_right) return false;
        }
        for(int i=0;i<other->getRight().size();i++) {
            bool in_right = false;
            for(int j=0;j<right.size();j++) {
                if (right[j].first->equates(other->getRight()[i].first)) {
                    in_right = true;
                    break;
                }
            }
            if(!in_right) return false;
        }
        for(int i=0;i<other->getLeft().size();i++) {
            bool in_left = false;
            for(int j=0;j<left.size();j++) {
                if (left[j].first->equates(other->getLeft()[i].first)) {
                    in_left = true;
                    break;
                }
            }
            if(!in_left) return false;
        }
        return true;
    }
    string getName() {
        string left_part = "";
        string right_part = "";

        for(int i=0;i<right.size();i++) {
            if(i==0)   right_part = right_part  + right[i].first->getName();
            else  right_part = right_part + ", " + right[i].first->getName();
        }
        for(int i=0;i<left.size();i++) {
            if(i==0) left_part = left_part  + left[i].first->getName();
            else  left_part = left_part + "," + left[i].first->getName();
        }
        if(left_part != "") left_part = left_part +" ";
        if(right_part != "") right_part = " " + right_part;
        return left_part+ "||--" + right_part;

    }

};



//proveSequentForProgram
bool proveSequent(shared_ptr<Sequent> sequent) {
    bool wohoo = false;
    for(int i=0;i<sequent->getLeft().size();i++) sequent->getLeft()[i].first->setInstantiationTime(0);
    for(int i=0;i<sequent->getRight().size();i++) sequent->getRight()[i].first->setInstantiationTime(0);
    vector<shared_ptr<Sequent>> frontier;
    frontier.push_back(sequent);
    vector<shared_ptr<Sequent>> proven={sequent};

    while (true) {
        shared_ptr<Sequent> old_sequent = nullptr;
        bool in_proven = false;
        for(int i=0; i<proven.size();i++) {
            if(old_sequent != nullptr && old_sequent->equates(proven[i])) {
                in_proven = true;
                break;
            }
        }
        while (frontier.size()>0 && (old_sequent == nullptr || in_proven)) {
            old_sequent = frontier[0];
            frontier.erase(frontier.begin());
         }
        if(old_sequent == nullptr) {
            break;
        }
         bool found = false;
        cout << old_sequent->getDepth()  << " " << old_sequent->getName() << "\n" ;
        for(int i=0;i<old_sequent->getLeft().size();i++) {
            for(int j=0; j<old_sequent->getRight().size();j++) {
                if(old_sequent->getLeft()[i].first->equates(old_sequent->getRight()[j].first)) {
                    found = true;
                    break;
                }
            }
        }
        if(found) {
            proven.push_back(old_sequent);
            continue;
        }
          //check if sequent has unification terms
        if(old_sequent->getSiblings().size() >0) {
            //get unifiable pairs for each sibling
            vector<vector<pair<shared_ptr<Container>,shared_ptr<Container>>>> sibling_pair_lists;
            for(int i=0; i<old_sequent->getSiblings().size();i++) {
                 sibling_pair_lists.push_back(old_sequent->getSiblings()[i]->getUnifiablePairs());
            }
            //check if there is a unifiable pair for each sibling
            bool there_is = true;
            for(int i=0; i<sibling_pair_lists.size(); i++) {

                if(sibling_pair_lists[i].size() <= 0) {
                     there_is = false;
                    break;
                }
            }
            if(there_is) {
                //iterate through all simultaneous choices of pairs from each sibling
                pair<vector<pair<shared_ptr<Container>,shared_ptr<Container>>>,bool> substitution = make_pair(vector<pair<shared_ptr<Container>,shared_ptr<Container>>>{},false);
                vector<int> index;
                for(int i=0; i<sibling_pair_lists.size(); i++) {
                    index.push_back(0);
                }
                while (true) {
                    //attempt to unify at the index
                    vector<pair<shared_ptr<Container>,shared_ptr< Container>>> temp;
                    for(int i=0; i<sibling_pair_lists.size();i++) {
                        temp.push_back(sibling_pair_lists[i][index[i]]);
                    }
                    substitution = unify_list(temp);
                    if (substitution.second != false ) {
                        break;
                    }
                    //increment the index
                    int pos = sibling_pair_lists.size() -1;
                    while (pos >= 0) {
                        index[pos] += 1;
                        if( index[pos] < sibling_pair_lists[pos].size()) break;
                        index[pos] = 0;
                        pos -= 1;
                    }
                    if(pos < 0) break;
                }
                if (substitution.second != false ) {
                    for(int j=0;j<substitution.first.size();j++) {
                        cout << " " << substitution.first[j].first->getName() << " = " << substitution.first[j].second->getName();
                    }
                    for(int i=0;i<old_sequent->getSiblings().size();i++) {
                        proven.push_back(old_sequent->getSiblings()[i]);
                    }
                    vector<shared_ptr<Sequent>> temp;
                    for(int i=0;i<frontier.size();i++) {
                        bool found = false;
                        for(int j=0;j<old_sequent->getSiblings().size();j++) {
                            if(frontier[i]->equates(old_sequent->getSiblings()[j])) {
                                found = true;
                                break;
                            }
                        }
                        if(!found) {
                            temp.push_back(frontier[i]);
                        }
                    }
                    frontier = temp;
                    continue;
                }
            }
            else {
                old_sequent->removeSibling(old_sequent);
            }
        }
        while(true) {
                //rule for logic K
                //necessary
            bool necessary = true;
            for(int i=0;i<old_sequent->getLeft().size();i++) {
                if(old_sequent->getLeft()[i].first->getCName() != "necessarily" ) {
                    necessary = false;
                    break;
                }
            }
            for(int i=0;i<old_sequent->getRight().size();i++) {
                if(old_sequent->getRight()[i].first->getCName() != "necessarily" ) {
                    necessary = false;
                    break;
                }
            }
            if(necessary) {
                 shared_ptr<Sequent> new_sequent = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                int broj = new_sequent->getLeft().size();
                for(int i=0; i<broj;i++) {
                    new_sequent->addLeft(make_pair(new_sequent->getLeft()[i].first->getFormula() ,old_sequent->getLeft()[i].second+1));
                }
                for(int i=0; i<broj; i++) {
                    new_sequent->eraseLeftAt(0);
                }
                broj = new_sequent->getRight().size();
                for(int i=0; i<broj;i++) {
                    new_sequent->addRight(make_pair(new_sequent->getRight()[i].first->getFormula() ,old_sequent->getRight()[i].second+1));
                }
                for(int i=0; i<broj; i++) {
                    new_sequent->eraseRightAt(0);
                }
                if ( new_sequent->getSiblings().size() >0) {
                    new_sequent->addSibling(new_sequent);
                }
                frontier.push_back(new_sequent);
                break;
            }
               //determine which formula to expand
            shared_ptr<Container> left_formula = nullptr;
            int left_depth = 0;
            for (int i=old_sequent->getLeft().size()-1;i>=0; i--) {
                 if(left_depth == 0 || left_depth > old_sequent->getLeft()[i].second)
                    {
                        if(!(old_sequent->getLeft()[i].first->getCName() == "predicate" ||  old_sequent->getLeft()[i].first->getCName() == "function" || old_sequent->getLeft()[i].first->getCName() == "variable" || old_sequent->getLeft()[i].first->getCName() == "unificationterm")) {
                            left_formula = old_sequent->getLeft()[i].first;
                            left_depth = old_sequent->getLeft()[i].second;
                        }
                    }
            }
            shared_ptr<Container> right_formula = nullptr;
            int right_depth = 0;
            for(int i=old_sequent->getRight().size()-1;i>=0; i--) {
                if(right_depth == 0 || right_depth > old_sequent->getRight()[i].second)
                    {
                        if(!(old_sequent->getRight()[i].first->getCName() == "predicate" || old_sequent->getRight()[i].first->getCName() == "necessarily" || old_sequent->getRight()[i].first->getCName() == "function" ||old_sequent->getRight()[i].first->getCName() == "variable" || old_sequent->getRight()[i].first->getCName() == "unificationterm")) {
                            right_formula = old_sequent->getRight()[i].first;
                            right_depth = old_sequent->getRight()[i].second;
                        }
                    }
            }
        bool apply_left = false;
        bool apply_right = false;
        if (left_formula != nullptr && right_formula == nullptr) apply_left = true;
        if (left_formula == nullptr && right_formula != nullptr) apply_right = true;
        if (left_formula != nullptr && right_formula != nullptr) {
            if(left_depth < right_depth) apply_left = true;
            else apply_right = true;
        }
        if (left_formula == nullptr && right_formula == nullptr) return false;

        if (apply_left) {

            if(left_formula->getCName() == "necessarily") {
               shared_ptr<Sequent> new_sequent = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                int find_ind =-1;
                for(int i=0;i<new_sequent->getLeft().size();i++) {
                    if(new_sequent->getLeft()[i].first->equates(left_formula)) find_ind = i;
                }
                if(find_ind != -1) new_sequent->eraseLeftAt(find_ind);
                else throw string("Greska apply left rule");
                new_sequent->addLeft(make_pair(left_formula->getFormula() ,old_sequent->getLeft()[find_ind].second+1));
                if ( new_sequent->getSiblings().size() >0) {
                    new_sequent->addSibling(new_sequent);
                }
                frontier.push_back(new_sequent);
                break;
            }

            if(left_formula->getCName() == "possibly") {
               shared_ptr<Sequent> new_sequent = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                int find_ind =-1;
                for(int i=0;i<new_sequent->getLeft().size();i++) {
                    if(new_sequent->getLeft()[i].first->equates(left_formula)) find_ind = i;
                }
                if(find_ind != -1) new_sequent->eraseLeftAt(find_ind);
                else throw string("Greska apply left rule");
                new_sequent->addRight(make_pair(make_shared<Necessarily>(make_shared<Not>(left_formula->getFormula())) ,old_sequent->getLeft()[find_ind].second+1));
                if ( new_sequent->getSiblings().size() >0) {
                    new_sequent->addSibling(new_sequent);
                }
                frontier.push_back(new_sequent);
                break;
            }
            if(left_formula->getCName() == "not") {
                shared_ptr<Sequent> new_sequent = make_shared<Sequent>( old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                int find_ind =-1;
                for(int i=0;i<new_sequent->getLeft().size();i++) {
                    if(new_sequent->getLeft()[i].first->equates(left_formula)) find_ind = i;
                }
                if(find_ind != -1) new_sequent->eraseLeftAt(find_ind);
                else throw string("Greska apply left rule");
                new_sequent->addRight(make_pair(left_formula->getFormula(),old_sequent->getLeft()[find_ind].second+1));
                if ( new_sequent->getSiblings().size() >0) {
                    new_sequent->addSibling(new_sequent);
                }
                frontier.push_back(new_sequent);
                break;
            }
            if(left_formula->getCName() == "and") {
                shared_ptr<Sequent> new_sequent = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                int find_ind =-1;
                for(int i=0;i<new_sequent->getLeft().size();i++) {
                    if(new_sequent->getLeft()[i].first->equates(left_formula)) find_ind = i;
                }
                if(find_ind != -1) new_sequent->eraseLeftAt(find_ind);
                else throw string("Greska apply left rule");
                new_sequent->addLeft(make_pair(left_formula->getFormulaA(),old_sequent->getLeft()[find_ind].second+1));
                new_sequent->addLeft(make_pair(left_formula->getFormulaB(),old_sequent->getLeft()[find_ind].second+1));
                if (new_sequent->getSiblings().size() >0) {
                    new_sequent->addSibling(new_sequent);
                }
                frontier.push_back(new_sequent);
                break;
            }
            if(left_formula->getCName() == "or") {
                shared_ptr<Sequent> new_sequent_a = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                shared_ptr<Sequent> new_sequent_b = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                int find_ind =-1;
                for(int i=0;i<new_sequent_a->getLeft().size();i++) {
                    if(new_sequent_a->getLeft()[i].first->equates(left_formula)) find_ind = i;
                }
                if(find_ind != -1) {new_sequent_a->eraseLeftAt(find_ind); new_sequent_b->eraseLeftAt(find_ind);}
                else throw string("Greska apply left rule");
                new_sequent_a->addLeft(make_pair(left_formula->getFormulaA(),old_sequent->getLeft()[find_ind].second+1));
                new_sequent_b->addLeft(make_pair(left_formula->getFormulaB(),old_sequent->getLeft()[find_ind].second+1));
                if ( new_sequent_a->getSiblings().size() >0) {
                    new_sequent_a->addSibling(new_sequent_a);
                }
                if ( new_sequent_b->getSiblings().size() >0) {
                    new_sequent_b->addSibling(new_sequent_b);
                }
                frontier.push_back(new_sequent_a);
                frontier.push_back(new_sequent_b);
                break;
            }
            if(left_formula->getCName() == "implies") {
                shared_ptr<Sequent> new_sequent_a = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                shared_ptr<Sequent> new_sequent_b = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                int find_ind =-1;
                for(int i=0;i<new_sequent_a->getLeft().size();i++) {
                    if(new_sequent_a->getLeft()[i].first->equates(left_formula)) find_ind = i;
                }
                if(find_ind != -1) {new_sequent_a->eraseLeftAt(find_ind); new_sequent_b->eraseLeftAt(find_ind);}
                else throw string("Greska apply left rule");
                new_sequent_a->addRight(make_pair(left_formula->getFormulaA(),old_sequent->getLeft()[find_ind].second+1));
                new_sequent_b->addLeft(make_pair(left_formula->getFormulaB(),old_sequent->getLeft()[find_ind].second+1));
                if ( new_sequent_a->getSiblings().size() >0) {
                    new_sequent_a->addSibling(new_sequent_a);
                }
                if ( new_sequent_b->getSiblings().size() >0) {
                    new_sequent_b->addSibling(new_sequent_b);
                }
                frontier.push_back(new_sequent_a);
                frontier.push_back(new_sequent_b);
                break;
            }
            if(left_formula->getCName() == "forall") {
                shared_ptr<Sequent> new_sequent = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                int find_ind =-1;
                for(int i=0;i<new_sequent->getLeft().size();i++) {
                    if(new_sequent->getLeft()[i].first->equates(left_formula)) find_ind = i;
                }
                new_sequent->setLeftDepth(find_ind,new_sequent->getLeft()[find_ind].second+1);
                shared_ptr<Container> formula = left_formula->getFormula()->replace(left_formula->getVariable(), make_shared<UnificationTerm>(old_sequent->getVariableName("t")));
                formula->setInstantiationTime(old_sequent->getDepth()+1);
                bool found = false;
                for(int i=0;i<new_sequent->getLeft().size();i++) {
                    if( formula->equates(new_sequent->getLeft()[i].first)) {
                        found = true;
                        break;
                    }
                }
                if(!found) {
                    new_sequent->addLeft(make_pair(formula,new_sequent->getLeft()[find_ind].second));
                }
              //  if(new_sequent->getSiblings().size() >0) {
                    new_sequent->addSibling(new_sequent);
                //}
                frontier.push_back(new_sequent);
                break;
            }
            if(left_formula->getCName() == "thereexists") {
                     shared_ptr<Sequent> new_sequent = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                int find_ind =-1;
                for(int i=0;i<new_sequent->getLeft().size();i++) {
                    if(new_sequent->getLeft()[i].first->equates(left_formula)) find_ind = i;
                }

                shared_ptr<Container> variable = make_shared<Variable>(old_sequent->getVariableName("v"),0);

                if(find_ind != -1) new_sequent->eraseLeftAt(find_ind);
                else throw string("Greska apply left rule");

                shared_ptr<Container> formula = left_formula->getFormula()->replace(left_formula->getVariable(), variable );
                formula->setInstantiationTime(old_sequent->getDepth()+1);
                new_sequent->addLeft(make_pair(formula,old_sequent->getLeft()[find_ind].second+1));
                if(new_sequent->getSiblings().size() >0) {
                    new_sequent->addSibling(new_sequent);
                }
                frontier.push_back(new_sequent);
                break;
            }
        }
        if (apply_right) {
             if(right_formula->getCName() == "possibly") {
                shared_ptr<Sequent> new_sequent = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                int find_ind =-1;
                for(int i=0;i<new_sequent->getRight().size();i++) {
                    if(new_sequent->getRight()[i].first->equates(right_formula)) find_ind = i;
                }
                if(find_ind != -1) new_sequent->eraseRightAt(find_ind);
                else throw string("Greska apply left rule");
                new_sequent->addLeft(make_pair(make_shared<Necessarily>(make_shared<Not>(right_formula->getFormula())) ,old_sequent->getRight()[find_ind].second+1));
                if ( new_sequent->getSiblings().size() >0) {
                    new_sequent->addSibling(new_sequent);
                }
                frontier.push_back(new_sequent);
                break;
            }
            if(right_formula->getCName() == "not") {

                shared_ptr<Sequent> new_sequent = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                int find_ind =-1;
                for(int i=0;i<new_sequent->getRight().size();i++) {
                    if(new_sequent->getRight()[i].first->equates(right_formula)) find_ind = i;
                }
                if(find_ind != -1) new_sequent->eraseRightAt(find_ind);
                else throw string("Greska apply left rule");
                new_sequent->addLeft(make_pair(right_formula->getFormula(),old_sequent->getRight()[find_ind].second+1));
                if ( new_sequent->getSiblings().size() >0) {
                    new_sequent->addSibling(new_sequent);
                }
                frontier.push_back(new_sequent);
                break;
            }
            if(right_formula->getCName() == "and") {
                shared_ptr<Sequent> new_sequent_a = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                shared_ptr<Sequent> new_sequent_b = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                int find_ind =-1;
                for(int i=0;i<new_sequent_a->getRight().size();i++) {
                    if(new_sequent_a->getRight()[i].first->equates(right_formula)) find_ind = i;
                }
                if(find_ind != -1) {new_sequent_a->eraseRightAt(find_ind); new_sequent_b->eraseRightAt(find_ind);}
                else throw string("Greska apply right rule");
                new_sequent_a->addRight(make_pair(right_formula->getFormulaA(),old_sequent->getRight()[find_ind].second+1));
                new_sequent_b->addRight(make_pair(right_formula->getFormulaB(),old_sequent->getRight()[find_ind].second+1));
                if ( new_sequent_a->getSiblings().size() >0) {
                    new_sequent_a->addSibling(new_sequent_a);
                }
                if ( new_sequent_b->getSiblings().size() >0) {
                    new_sequent_b->addSibling(new_sequent_b);
                }
                frontier.push_back(new_sequent_a);
                frontier.push_back(new_sequent_b);
                break;
            }
            if(right_formula->getCName() == "or") {
                shared_ptr<Sequent> new_sequent = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                int find_ind =-1;
                for(int i=0;i<new_sequent->getRight().size();i++) {
                    if(new_sequent->getRight()[i].first->equates(right_formula)) find_ind = i;
                }

                if(find_ind != -1) new_sequent->eraseRightAt(find_ind);
                else throw string("Greska apply right rule");
                new_sequent->addRight(make_pair(right_formula->getFormulaA(),old_sequent->getRight()[find_ind].second+1));
                new_sequent->addRight(make_pair(right_formula->getFormulaB(),old_sequent->getRight()[find_ind].second+1));

                if (new_sequent->getSiblings().size() >0) {
                    new_sequent->addSibling(new_sequent);
                }
                frontier.push_back(new_sequent);

                wohoo =true;
                break;
            }
            if(right_formula->getCName() == "implies") {
                shared_ptr<Sequent> new_sequent = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                int find_ind =-1;
                for(int i=0;i<new_sequent->getRight().size();i++) {
                    if(new_sequent->getRight()[i].first->equates(right_formula)) find_ind = i;
                }
                if(find_ind != -1) new_sequent->eraseRightAt(find_ind);
                else throw string("Greska apply right rule");
                new_sequent->addLeft(make_pair(right_formula->getFormulaA(),old_sequent->getRight()[find_ind].second+1));
                new_sequent->addRight(make_pair(right_formula->getFormulaB(),old_sequent->getRight()[find_ind].second+1));
               // if (new_sequent->getSiblings().size() >0) {
                    new_sequent->addSibling(new_sequent);
                //}
                frontier.push_back(new_sequent);
                break;
            }
            if(right_formula->getCName() == "forall") {
                shared_ptr<Sequent> new_sequent = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                int find_ind =-1;
                for(int i=0;i<new_sequent->getRight().size();i++) {
                    if(new_sequent->getRight()[i].first->equates(right_formula)) find_ind = i;
                }
                if(find_ind != -1) { new_sequent->eraseRightAt(find_ind); }
                else throw string("Greska apply right rule");
                shared_ptr<Container> variable = make_shared<Variable>(old_sequent->getVariableName("v"),0);
                shared_ptr<Container> formula = right_formula->getFormula()->replace(right_formula->getVariable(), variable );
                formula->setInstantiationTime(old_sequent->getDepth()+1);
                new_sequent->addRight(make_pair(formula,old_sequent->getRight()[find_ind].second+1));
              //  if(new_sequent->getSiblings().size() >0) {
                    new_sequent->addSibling(new_sequent);
                //}
                frontier.push_back(new_sequent);
                break;
            }


            if(right_formula->getCName() == "thereexists") {
                        shared_ptr<Sequent> new_sequent = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                int find_ind =-1;
                for(int i=0;i<new_sequent->getRight().size();i++) {
                    if(new_sequent->getRight()[i].first->equates(right_formula)) find_ind = i;
                }

                new_sequent->setRightDepth(find_ind,new_sequent->getRight()[find_ind].second+1);
                int d = new_sequent->getRight()[find_ind].second+1;
                shared_ptr<Container> formula = right_formula->getFormula()->replace(right_formula->getVariable(), make_shared<UnificationTerm>(old_sequent->getVariableName("t")));
                formula->setInstantiationTime(old_sequent->getDepth()+1);
                bool found = false;


                for(int i=0;i<new_sequent->getRight().size();i++) {
                    if( formula->equates(new_sequent->getRight()[i].first)) {
                        found = true;
                        break;
                    }
                }
                if(!found) {
                    new_sequent->addRight(make_pair(formula,new_sequent->getRight()[find_ind].second));
                }

               // if(new_sequent->getSiblings().size() >0) {
                    new_sequent->addSibling(new_sequent);
               // }

                frontier.push_back(new_sequent);

                break;
            }
        }
        }
}

return true;
}
//function that proves formula
bool proveFormula2(vector<shared_ptr<Container >> axioms, shared_ptr<Container> formula) {
    vector<pair<shared_ptr<Container>,int>> temp;
    for(int i=0;i<axioms.size();i++) {
        temp.push_back(make_pair(axioms[i],0));
    }
     vector<pair<shared_ptr<Container>,int>> temp2;
     temp2.push_back(make_pair(formula,0));

    return proveSequent(make_shared<Sequent>(temp,temp2,vector<shared_ptr<Sequent>>{},0));
}
//Prover's function that proves formula
//Prover's all functions
void Prover::proveFormula(vector<string> s) {
        shared_ptr<Container> formula = parse(s);
                vector<shared_ptr<Container>> temp2;
                for(int k=0;k<axioms.size();k++) temp2.push_back(axioms[k]);
                for(int k=0;k<lemmas.size();k++) temp2.push_back(lemmas[k].first);

                bool result = proveFormula2(temp2,formula);
                if (result) {
                    cout << "\nFormula proven\n";
                }
                else {
                    cout << "\nFormula unprovable\n";
                }

    }
    string Prover::getAxioms() {
        string a = " ";
        for (int i=0; i<axioms.size();i++) {
                a = a + ", " + axioms[i]->getName();
        }
        return a;
    }
    string Prover::getLemmas() {
        string a = " ";
        for(int i=0; i<lemmas.size();i++) {
                    a = a + ", " + lemmas[i].first->getName();
                }
        return a;
    }
    void Prover::addAxioms(vector<string> a) {
         shared_ptr<Container> formula = parse(a);
                axioms.push_back(formula);
                cout << "Axiom added: \n" << formula->getName();
    }
    bool  Prover::addLemma(vector<string> l) {
         shared_ptr<Container> formula = parse(l);
                //prove formula
                vector<shared_ptr<Container>> temp2;
                for(int k=0;k<axioms.size();k++) temp2.push_back(axioms[k]);
                for(int k=0;k<lemmas.size();k++) temp2.push_back(lemmas[k].first);
                bool result = proveFormula2(temp2,formula);
                if (result) {
                    lemmas.push_back(make_pair(formula,axioms));
                    cout << "\nlemma proven\n" << formula->getName();
                }
                else {
                    cout << "Lemma unprovable\n";
                }
    }


//proveSequent function for testing
pair<pair<bool,int>,int> proveSequentTest(shared_ptr<Sequent> sequent) {
    bool wohoo = false;
     for(int i=0;i<sequent->getLeft().size();i++) sequent->getLeft()[i].first->setInstantiationTime(0);
    for(int i=0;i<sequent->getRight().size();i++) sequent->getRight()[i].first->setInstantiationTime(0);
    vector<shared_ptr<Sequent>> frontier;
    frontier.push_back(sequent);
    vector<shared_ptr<Sequent>> proven={sequent};
    int depth_test = 0;
    int steps_test = 0;

    while (true) {
        shared_ptr<Sequent> old_sequent = nullptr;
        bool in_proven = false;
        for(int i=0; i<proven.size();i++) {
            if(old_sequent != nullptr && old_sequent->equates(proven[i])) {
                in_proven = true;
                break;
            }
        }
        while (frontier.size()>0 && (old_sequent == nullptr || in_proven)) {
            old_sequent = frontier[0];
            frontier.erase(frontier.begin());
         }
        if(old_sequent == nullptr) {
            break;
        }

         bool found = false;

        cout << old_sequent->getDepth() << " " << old_sequent->getName() << "\n" ;
        depth_test = old_sequent->getDepth();
        steps_test ++;


        for(int i=0;i<old_sequent->getLeft().size();i++) {
            for(int j=0; j<old_sequent->getRight().size();j++) {
                if(old_sequent->getLeft()[i].first->equates(old_sequent->getRight()[j].first)) {

                    found = true;
                    break;
                }
            }
        }
        if(found) {
            proven.push_back(old_sequent);

            continue;
        }

          //check if sequent has unification terms
        if(old_sequent->getSiblings().size() >0) {

            //get unifiable pairs for each sibling
            vector<vector<pair<shared_ptr<Container>,shared_ptr<Container>>>> sibling_pair_lists;
            for(int i=0; i<old_sequent->getSiblings().size();i++) {
                 sibling_pair_lists.push_back(old_sequent->getSiblings()[i]->getUnifiablePairs());
            }
            //check if there is a unifiable pair for each sibling
            bool there_is = true;
            for(int i=0; i<sibling_pair_lists.size(); i++) {

                if(sibling_pair_lists[i].size() <= 0) {
                     there_is = false;
                    break;
                }
            }
            if(there_is) {

                //iterate through all simultaneous choices of pairs from each sibling
                pair<vector<pair<shared_ptr<Container>,shared_ptr<Container>>>,bool> substitution = make_pair(vector<pair<shared_ptr<Container>,shared_ptr<Container>>>{},false);
                vector<int> index;
                for(int i=0; i<sibling_pair_lists.size(); i++) {
                    index.push_back(0);
                }
                while (true) {
                    //attempt to unify at the index
                    vector<pair<shared_ptr<Container>,shared_ptr< Container>>> temp;
                    for(int i=0; i<sibling_pair_lists.size();i++) {
                        temp.push_back(sibling_pair_lists[i][index[i]]);
                    }
                    substitution = unify_list(temp);
                    if (substitution.second != false ) {
                        break;
                    }
                    //increment the index
                    int pos = sibling_pair_lists.size() -1;
                    while (pos >= 0) {
                        index[pos] += 1;
                        if( index[pos] < sibling_pair_lists[pos].size()) break;
                        index[pos] = 0;
                        pos -= 1;
                    }
                    if(pos < 0) break;
                }
                if (substitution.second != false ) {
                    for(int j=0;j<substitution.first.size();j++) {
                        cout << " " << substitution.first[j].first->getName() << " = " << substitution.first[j].second->getName();
                    }
                    for(int i=0;i<old_sequent->getSiblings().size();i++) {
                        proven.push_back(old_sequent->getSiblings()[i]);
                    }
                    vector<shared_ptr<Sequent>> temp;
                    for(int i=0;i<frontier.size();i++) {
                            bool found = false;
                        for(int j=0;j<old_sequent->getSiblings().size();j++) {
                            if(frontier[i]->equates(old_sequent->getSiblings()[j])) {
                                found = true;
                                break;
                            }
                        }
                        if(!found) {
                            temp.push_back(frontier[i]);
                        }
                    }
                    frontier = temp;
                    continue;
                }

            }
            else {

                old_sequent->removeSibling(old_sequent);
            }
        }



        while(true) {
                //rule for logic K
                //necessary
                bool necessary = true;
        for(int i=0;i<old_sequent->getLeft().size();i++) {
            if(old_sequent->getLeft()[i].first->getCName() != "necessarily" ) {
                necessary = false;
                break;
            }
        }
        for(int i=0;i<old_sequent->getRight().size();i++) {
            if(old_sequent->getRight()[i].first->getCName() != "necessarily" ) {
                necessary = false;
                break;
            }
        }

        if(necessary) {

             shared_ptr<Sequent> new_sequent = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                int broj = new_sequent->getLeft().size();
                for(int i=0; i<broj;i++) {
                     new_sequent->addLeft(make_pair(new_sequent->getLeft()[i].first->getFormula() ,old_sequent->getLeft()[i].second+1));
                }

                for(int i=0; i<broj; i++) {
                    new_sequent->eraseLeftAt(0);
                }

                broj = new_sequent->getRight().size();
                for(int i=0; i<broj;i++) {
                     new_sequent->addRight(make_pair(new_sequent->getRight()[i].first->getFormula() ,old_sequent->getRight()[i].second+1));
                }
                for(int i=0; i<broj; i++) {
                    new_sequent->eraseRightAt(0);
                }


                if ( new_sequent->getSiblings().size() >0) {
                    new_sequent->addSibling(new_sequent);
                }
                frontier.push_back(new_sequent);

                break;
        }


               //determine which formula to expand
            shared_ptr<Container> left_formula = nullptr;
            int left_depth = 0;
            for (int i=old_sequent->getLeft().size()-1;i>=0; i--) {
                 if(left_depth == 0 || left_depth > old_sequent->getLeft()[i].second)
                    {
                        if(!(old_sequent->getLeft()[i].first->getCName() == "predicate" ||  old_sequent->getLeft()[i].first->getCName() == "function" || old_sequent->getLeft()[i].first->getCName() == "variable" || old_sequent->getLeft()[i].first->getCName() == "unificationterm")) {
                            left_formula = old_sequent->getLeft()[i].first;
                            left_depth = old_sequent->getLeft()[i].second;


                        }
                    }

            }

            shared_ptr<Container> right_formula = nullptr;
            int right_depth = 0;
           for(int i=old_sequent->getRight().size()-1;i>=0; i--) {

                if(right_depth == 0 || right_depth > old_sequent->getRight()[i].second)
                    {
                        if(!(old_sequent->getRight()[i].first->getCName() == "predicate" || old_sequent->getRight()[i].first->getCName() == "necessarily" || old_sequent->getRight()[i].first->getCName() == "function" ||old_sequent->getRight()[i].first->getCName() == "variable" || old_sequent->getRight()[i].first->getCName() == "unificationterm")) {
                            right_formula = old_sequent->getRight()[i].first;
                            right_depth = old_sequent->getRight()[i].second;


                        }
                    }

            }


        bool apply_left = false;
        bool apply_right = false;
        if (left_formula != nullptr && right_formula == nullptr) apply_left = true;
        if (left_formula == nullptr && right_formula != nullptr) apply_right = true;
        if (left_formula != nullptr && right_formula != nullptr) {
            if(left_depth < right_depth) apply_left = true;
            else apply_right = true;
        }
        if (left_formula == nullptr && right_formula == nullptr) return make_pair(make_pair(false,depth_test),steps_test);


        if (apply_left) {

            if(left_formula->getCName() == "necessarily") {


               shared_ptr<Sequent> new_sequent = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                int find_ind =-1;
                for(int i=0;i<new_sequent->getLeft().size();i++) {
                    if(new_sequent->getLeft()[i].first->equates(left_formula)) find_ind = i;
                }
                if(find_ind != -1) new_sequent->eraseLeftAt(find_ind);
                else throw string("Greska apply left rule");
                new_sequent->addLeft(make_pair(left_formula->getFormula() ,old_sequent->getLeft()[find_ind].second+1));
                if ( new_sequent->getSiblings().size() >0) {
                    new_sequent->addSibling(new_sequent);
                }
                frontier.push_back(new_sequent);
                break;
            }

            if(left_formula->getCName() == "possibly") {


               shared_ptr<Sequent> new_sequent = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                int find_ind =-1;
                for(int i=0;i<new_sequent->getLeft().size();i++) {
                    if(new_sequent->getLeft()[i].first->equates(left_formula)) find_ind = i;
                }
                if(find_ind != -1) new_sequent->eraseLeftAt(find_ind);
                else throw string("Greska apply left rule");
                new_sequent->addRight(make_pair(make_shared<Necessarily>(make_shared<Not>(left_formula->getFormula())) ,old_sequent->getLeft()[find_ind].second+1));
                if ( new_sequent->getSiblings().size() >0) {
                    new_sequent->addSibling(new_sequent);
                }
                frontier.push_back(new_sequent);
                break;
            }
            if(left_formula->getCName() == "not") {


                shared_ptr<Sequent> new_sequent = make_shared<Sequent>( old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                int find_ind =-1;
                for(int i=0;i<new_sequent->getLeft().size();i++) {
                    if(new_sequent->getLeft()[i].first->equates(left_formula)) find_ind = i;
                }
                if(find_ind != -1) new_sequent->eraseLeftAt(find_ind);
                else throw string("Greska apply left rule");
                new_sequent->addRight(make_pair(left_formula->getFormula(),old_sequent->getLeft()[find_ind].second+1));
                if ( new_sequent->getSiblings().size() >0) {
                    new_sequent->addSibling(new_sequent);
                }
                frontier.push_back(new_sequent);
                break;
            }
            if(left_formula->getCName() == "and") {

                shared_ptr<Sequent> new_sequent = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                int find_ind =-1;
                for(int i=0;i<new_sequent->getLeft().size();i++) {
                    if(new_sequent->getLeft()[i].first->equates(left_formula)) find_ind = i;
                }
                if(find_ind != -1) new_sequent->eraseLeftAt(find_ind);
                else throw string("Greska apply left rule");
                new_sequent->addLeft(make_pair(left_formula->getFormulaA(),old_sequent->getLeft()[find_ind].second+1));
                new_sequent->addLeft(make_pair(left_formula->getFormulaB(),old_sequent->getLeft()[find_ind].second+1));
                if (new_sequent->getSiblings().size() >0) {
                    new_sequent->addSibling(new_sequent);
                }
                frontier.push_back(new_sequent);
                break;
            }
            if(left_formula->getCName() == "or") {

                shared_ptr<Sequent> new_sequent_a = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                shared_ptr<Sequent> new_sequent_b = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);

                int find_ind =-1;
                for(int i=0;i<new_sequent_a->getLeft().size();i++) {
                    if(new_sequent_a->getLeft()[i].first->equates(left_formula)) find_ind = i;
                }
                if(find_ind != -1) {new_sequent_a->eraseLeftAt(find_ind); new_sequent_b->eraseLeftAt(find_ind);}
                else throw string("Greska apply left rule");
                new_sequent_a->addLeft(make_pair(left_formula->getFormulaA(),old_sequent->getLeft()[find_ind].second+1));
                new_sequent_b->addLeft(make_pair(left_formula->getFormulaB(),old_sequent->getLeft()[find_ind].second+1));
                if ( new_sequent_a->getSiblings().size() >0) {
                    new_sequent_a->addSibling(new_sequent_a);
                }
                if ( new_sequent_b->getSiblings().size() >0) {
                    new_sequent_b->addSibling(new_sequent_b);
                }
                frontier.push_back(new_sequent_a);
                frontier.push_back(new_sequent_b);
                break;
            }
            if(left_formula->getCName() == "implies") {
                shared_ptr<Sequent> new_sequent_a = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                shared_ptr<Sequent> new_sequent_b = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);

                int find_ind =-1;
                for(int i=0;i<new_sequent_a->getLeft().size();i++) {
                    if(new_sequent_a->getLeft()[i].first->equates(left_formula)) find_ind = i;
                }
                if(find_ind != -1) {new_sequent_a->eraseLeftAt(find_ind); new_sequent_b->eraseLeftAt(find_ind);}
                else throw string("Greska apply left rule");
                new_sequent_a->addRight(make_pair(left_formula->getFormulaA(),old_sequent->getLeft()[find_ind].second+1));
                new_sequent_b->addLeft(make_pair(left_formula->getFormulaB(),old_sequent->getLeft()[find_ind].second+1));
                if ( new_sequent_a->getSiblings().size() >0) {
                    new_sequent_a->addSibling(new_sequent_a);
                }
                if ( new_sequent_b->getSiblings().size() >0) {
                    new_sequent_b->addSibling(new_sequent_b);
                }
                frontier.push_back(new_sequent_a);
                frontier.push_back(new_sequent_b);
                break;
            }
            if(left_formula->getCName() == "forall") {
                shared_ptr<Sequent> new_sequent = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                int find_ind =-1;
                for(int i=0;i<new_sequent->getLeft().size();i++) {
                    if(new_sequent->getLeft()[i].first->equates(left_formula)) find_ind = i;
                }
                 new_sequent->setLeftDepth(find_ind,new_sequent->getLeft()[find_ind].second+1);

                shared_ptr<Container> formula = left_formula->getFormula()->replace(left_formula->getVariable(), make_shared<UnificationTerm>(old_sequent->getVariableName("t")));
                formula->setInstantiationTime(old_sequent->getDepth()+1);
                bool found = false;
                for(int i=0;i<new_sequent->getLeft().size();i++) {
                    if( formula->equates(new_sequent->getLeft()[i].first)) {
                        found = true;
                        break;
                    }
                }
                if(!found) {
                    new_sequent->addLeft(make_pair(formula,new_sequent->getLeft()[find_ind].second));
                }
              //  if(new_sequent->getSiblings().size() >0) {
                    new_sequent->addSibling(new_sequent);
                //}
                frontier.push_back(new_sequent);
                break;
            }
            if(left_formula->getCName() == "thereexists") {
                     shared_ptr<Sequent> new_sequent = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                int find_ind =-1;
                for(int i=0;i<new_sequent->getLeft().size();i++) {
                    if(new_sequent->getLeft()[i].first->equates(left_formula)) find_ind = i;
                }

                shared_ptr<Container> variable = make_shared<Variable>(old_sequent->getVariableName("v"),0);

                if(find_ind != -1) new_sequent->eraseLeftAt(find_ind);
                else throw string("Greska apply left rule");

                shared_ptr<Container> formula = left_formula->getFormula()->replace(left_formula->getVariable(), variable );
                formula->setInstantiationTime(old_sequent->getDepth()+1);
                new_sequent->addLeft(make_pair(formula,old_sequent->getLeft()[find_ind].second+1));


                if(new_sequent->getSiblings().size() >0) {
                    new_sequent->addSibling(new_sequent);
                }
                frontier.push_back(new_sequent);
                break;
            }
        }

             if (apply_right) {

             if(right_formula->getCName() == "possibly") {

                shared_ptr<Sequent> new_sequent = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                int find_ind =-1;
                for(int i=0;i<new_sequent->getRight().size();i++) {
                    if(new_sequent->getRight()[i].first->equates(right_formula)) find_ind = i;
                }
                if(find_ind != -1) new_sequent->eraseRightAt(find_ind);
                else throw string("Greska apply left rule");
                new_sequent->addLeft(make_pair(make_shared<Necessarily>(make_shared<Not>(right_formula->getFormula())) ,old_sequent->getRight()[find_ind].second+1));
                if ( new_sequent->getSiblings().size() >0) {
                    new_sequent->addSibling(new_sequent);
                }
                frontier.push_back(new_sequent);
                break;
            }
            if(right_formula->getCName() == "not") {

                shared_ptr<Sequent> new_sequent = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                int find_ind =-1;
                for(int i=0;i<new_sequent->getRight().size();i++) {
                    if(new_sequent->getRight()[i].first->equates(right_formula)) find_ind = i;
                }
                if(find_ind != -1) new_sequent->eraseRightAt(find_ind);
                else throw string("Greska apply left rule");
                new_sequent->addLeft(make_pair(right_formula->getFormula(),old_sequent->getRight()[find_ind].second+1));
                if ( new_sequent->getSiblings().size() >0) {
                    new_sequent->addSibling(new_sequent);
                }
                frontier.push_back(new_sequent);
                break;
            }
            if(right_formula->getCName() == "and") {

                shared_ptr<Sequent> new_sequent_a = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                shared_ptr<Sequent> new_sequent_b = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);

                int find_ind =-1;
                for(int i=0;i<new_sequent_a->getRight().size();i++) {
                    if(new_sequent_a->getRight()[i].first->equates(right_formula)) find_ind = i;
                }
                if(find_ind != -1) {new_sequent_a->eraseRightAt(find_ind); new_sequent_b->eraseRightAt(find_ind);}
                else throw string("Greska apply right rule");
                new_sequent_a->addRight(make_pair(right_formula->getFormulaA(),old_sequent->getRight()[find_ind].second+1));
                new_sequent_b->addRight(make_pair(right_formula->getFormulaB(),old_sequent->getRight()[find_ind].second+1));
                if ( new_sequent_a->getSiblings().size() >0) {
                    new_sequent_a->addSibling(new_sequent_a);
                }
                if ( new_sequent_b->getSiblings().size() >0) {
                    new_sequent_b->addSibling(new_sequent_b);
                }
                frontier.push_back(new_sequent_a);
                frontier.push_back(new_sequent_b);
                break;

            }
            if(right_formula->getCName() == "or") {

                shared_ptr<Sequent> new_sequent = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                int find_ind =-1;
                for(int i=0;i<new_sequent->getRight().size();i++) {
                    if(new_sequent->getRight()[i].first->equates(right_formula)) find_ind = i;
                }

                if(find_ind != -1) new_sequent->eraseRightAt(find_ind);
                else throw string("Greska apply right rule");
                new_sequent->addRight(make_pair(right_formula->getFormulaA(),old_sequent->getRight()[find_ind].second+1));
                new_sequent->addRight(make_pair(right_formula->getFormulaB(),old_sequent->getRight()[find_ind].second+1));

                if (new_sequent->getSiblings().size() >0) {
                    new_sequent->addSibling(new_sequent);
                }
                frontier.push_back(new_sequent);

                wohoo =true;
                break;
            }
            if(right_formula->getCName() == "implies") {

                shared_ptr<Sequent> new_sequent = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                int find_ind =-1;
                for(int i=0;i<new_sequent->getRight().size();i++) {
                    if(new_sequent->getRight()[i].first->equates(right_formula)) find_ind = i;
                }
                if(find_ind != -1) new_sequent->eraseRightAt(find_ind);
                else throw string("Greska apply right rule");
                new_sequent->addLeft(make_pair(right_formula->getFormulaA(),old_sequent->getRight()[find_ind].second+1));
                new_sequent->addRight(make_pair(right_formula->getFormulaB(),old_sequent->getRight()[find_ind].second+1));
               // if (new_sequent->getSiblings().size() >0) {
                    new_sequent->addSibling(new_sequent);
                //}
                frontier.push_back(new_sequent);
                break;
            }
            if(right_formula->getCName() == "forall") {

                shared_ptr<Sequent> new_sequent = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                int find_ind =-1;

                for(int i=0;i<new_sequent->getRight().size();i++) {

                    if(new_sequent->getRight()[i].first->equates(right_formula)) find_ind = i;
                }

                 if(find_ind != -1) { new_sequent->eraseRightAt(find_ind); }
                else throw string("Greska apply right rule");
                 shared_ptr<Container> variable = make_shared<Variable>(old_sequent->getVariableName("v"),0);

                shared_ptr<Container> formula = right_formula->getFormula()->replace(right_formula->getVariable(), variable );
                formula->setInstantiationTime(old_sequent->getDepth()+1);
                new_sequent->addRight(make_pair(formula,old_sequent->getRight()[find_ind].second+1));


              //  if(new_sequent->getSiblings().size() >0) {
                    new_sequent->addSibling(new_sequent);
                //}
                frontier.push_back(new_sequent);
                break;
            }

            }
            if(right_formula->getCName() == "thereexists") {
                        shared_ptr<Sequent> new_sequent = make_shared<Sequent>(old_sequent->getLeft(),old_sequent->getRight(),old_sequent->getSiblings(),old_sequent->getDepth()+1);
                int find_ind =-1;
                for(int i=0;i<new_sequent->getRight().size();i++) {
                    if(new_sequent->getRight()[i].first->equates(right_formula)) find_ind = i;
                }

                new_sequent->setRightDepth(find_ind,new_sequent->getRight()[find_ind].second+1);
                int d = new_sequent->getRight()[find_ind].second+1;
                shared_ptr<Container> formula = right_formula->getFormula()->replace(right_formula->getVariable(), make_shared<UnificationTerm>(old_sequent->getVariableName("t")));
                formula->setInstantiationTime(old_sequent->getDepth()+1);
                bool found = false;


                for(int i=0;i<new_sequent->getRight().size();i++) {
                    if( formula->equates(new_sequent->getRight()[i].first)) {
                        found = true;
                        break;
                    }
                }
                if(!found) {
                    new_sequent->addRight(make_pair(formula,new_sequent->getRight()[find_ind].second));
                }

               // if(new_sequent->getSiblings().size() >0) {
                    new_sequent->addSibling(new_sequent);
               // }

                frontier.push_back(new_sequent);

                break;
            }


        }



}


return make_pair(make_pair(true,depth_test),steps_test);
        }
pair<pair<bool,int>,int> proveFormulaTest(vector<shared_ptr<Container >> axioms, shared_ptr<Container> formula) {

    vector<pair<shared_ptr<Container>,int>> temp;
    for(int i=0;i<axioms.size();i++) {
        temp.push_back(make_pair(axioms[i],0));
    }
     vector<pair<shared_ptr<Container>,int>> temp2;
     temp2.push_back(make_pair(formula,0));

    return proveSequentTest(make_shared<Sequent>(temp,temp2,vector<shared_ptr<Sequent>>{},0));
}


   pair<pair<bool,int>,int> Prover::proveFormulatest(vector<string> s) {
       shared_ptr<Container> formula = parse(s);
                vector<shared_ptr<Container>> temp2;
            for(int k=0;k<axioms.size();k++) temp2.push_back(axioms[k]);
                for(int k=0;k<lemmas.size();k++) temp2.push_back(lemmas[k].first);

             cout << "\n" << "Formula: " << formula->getName() << "\n" ;
            pair<pair<bool,int>,int> result = proveFormulaTest(temp2,formula);
            return result;
   }

