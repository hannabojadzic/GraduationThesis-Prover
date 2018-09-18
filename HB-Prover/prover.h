#ifndef PROVER_H
#define PROVER_H

#include <iostream>
#include <string>
#include <vector>
#include <exception>
#include <sstream>
#include <memory>
#include <chrono>
#include <thread>
#include <fstream>

using namespace std;
class Container {
public:
    string c_name;
    Container(string c_namep) {
        c_name = c_namep;
    };
    virtual bool occurs(shared_ptr<Container> unification_term) = 0;
    virtual void setInstantiationTime(double timep) = 0;
    virtual shared_ptr<Container> replace(shared_ptr<Container> old, shared_ptr<Container> neww) = 0;
    virtual vector<shared_ptr<Container>> freeUnificationTerms()  = 0;
    virtual vector<shared_ptr<Container>> freeVariables()  = 0;
    virtual string getName()  = 0;
    virtual bool equates( shared_ptr<Container> other) = 0;
    virtual string getCName() = 0;
    virtual vector<shared_ptr<Container> > getTerms()= 0;
    virtual shared_ptr<Container> getFormula()  = 0;
    virtual shared_ptr<Container> getFormulaA()  = 0;
    virtual shared_ptr<Container> getFormulaB()  = 0;
    virtual shared_ptr<Container> getVariable() = 0;
    virtual int getTime() = 0;

};
class Prover  {
public:
    vector<shared_ptr<Container>> axioms ={};
    vector<pair<shared_ptr<Container >,vector<shared_ptr<Container >>>> lemmas = {};

    void proveFormula(vector<string> s);
    string getAxioms();
    string getLemmas();
    void addAxioms(vector<string> a);
    bool  addLemma(vector<string> l);
    pair<pair<bool,int>,int> proveFormulatest(vector<string> s);
};
#endif
