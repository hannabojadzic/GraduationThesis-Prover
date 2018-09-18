
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

vector<string> lex(string inp) {
    vector<string> tokens = {};
    int pos = 0;
    while (pos < inp.length()) {
        //skip whitespace
        if (inp[pos] == ' ') {
            pos +=1;
            continue;
        }
        //identifiers
        string identifier = "";
        while (pos < inp.length() && isalnum(inp[pos])) {
            identifier = identifier + inp[pos];
            pos +=1;
        }
        if (identifier.length() > 0) {
            tokens.push_back(identifier);
            continue;
        }
        //symbols
        stringstream out;
        out << inp[pos];
        string s = "" + inp[pos];
        tokens.push_back(out.str());
        pos += 1;
    }
return tokens;
}
/*
int main()
{
    Prover *p = new Prover();
    cout << "Formulae: \n";
    cout << "P(term)         - predicate\n";
    cout << "not P           - complement\n";
    cout << "P or Q          - disjunction\n";
    cout << "P and Q         - conjuction\n";
    cout << "P implies Q     - implication\n";
    cout << "necessarily P   - necessity\n";
    cout << "possibly P      - possibility\n";
    cout << "forall x. P     - universal quantification\n";
    cout << "exists x. P     - existential quantification\n";
    cout << "\nEnter formulae. The following commands also available:\n";
    cout << "axioms          - list axioms\n";
    cout << "lemmas          - list lemmas\n";
    cout << "axiom <formula> - add an axiom\n";
    cout << "lemma <formula> - prove and add a lemma\n";

    while(1) {
        try {
            cout << "\nInput:\n";
            string inp;
            getline(cin, inp);
            vector<string> commands = {"axiom","lemma","axioms","lemmas","remove","reset"};
            vector<string> tokens = lex(inp);
            for (int i=1; i<tokens.size(); i++) {
                for(int j=0; j<commands.size();j++) {
                    if(tokens[i]==commands[j]) throw string("Unexpected keyword");
                }
            }
            if( tokens.size()>0 && tokens[0]== "axioms") {
                    if(tokens.size()>1) throw string("Unexpected token");
                  cout <<  p->getAxioms();
            }
            else if (tokens.size() > 0 && tokens[0]=="lemmas") {
                if(tokens.size()>1) throw string("Unexpected token");
                cout << p->getLemmas();
            }
            else if(tokens.size()>0 and tokens[0]=="axiom") {
                vector<string> temp;
                for(int i=1;i<tokens.size();i++) temp.push_back(tokens[i]);
                p->addAxioms(temp);
            }
            else if(tokens.size()>0 and tokens[0]=="lemma") {
                vector<string> temp;
                for(int i=1;i<tokens.size();i++) temp.push_back(tokens[i]);
                p->addLemma(temp);
            }
            else if(tokens.size()>0 and tokens[0]=="remove") {
            }
            else if(tokens.size()>0 and tokens[0]=="reset") {
            }
            else {
                p->proveFormula(tokens);
            }
            cout << "\n\n";
        }
        catch(string e){
            cout << e;
        }
        catch(exception e) {
            cout << "Greska";
        }
    }
    return 0;
}
*/
