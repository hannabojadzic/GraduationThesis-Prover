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


pair<vector<string>,int> lexTest(string inp) {
    int velicina = 0;
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
            velicina ++;
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
    return make_pair(tokens,velicina);
}

int main()
{

    char filename[ ] = "out.txt";
     fstream appendFileToWorkWith;

     appendFileToWorkWith.open(filename, std::fstream::in | std::fstream::out );

        bool postoji = true;
     // If file does not exist, Create new file
      if (!appendFileToWorkWith )
      {
        appendFileToWorkWith.open(filename,  fstream::in | fstream::out | fstream::trunc);
          postoji = false;

       }
Prover *p = new Prover();
    try {
        ifstream infile;
        infile.open ("theorems.txt");
        string STRING;
        while(!infile.eof()) // To get you all the lines.
        {
            getline(infile,STRING); // Saves the line in STRING.
            pair<vector<string>,int> tokens = lexTest(STRING);
            pair<pair<bool,int>,int> result = p->proveFormulatest(tokens.first);
            if (result.first.first) {
                if(postoji == false) {
                        cout < "HDWODWOEJDPOWQPDOKP\nDODPKQOWKPO\nkfwoekpfwo";
                    appendFileToWorkWith << "\n Formula: " << STRING;
                    appendFileToWorkWith << "\nFormula proven";
                    appendFileToWorkWith << "\n" << "Dubina stabla: "  << result.first.second;
                    appendFileToWorkWith << "\n" << "Broj koraka izvrsavanja: " << result.second;
                    appendFileToWorkWith << "\n" << "Broj operatora i literala u formuli: " <<tokens.second << "\n";

                }
                cout << "\nFormula proven\n";
                cout << "\n" << "Dubina stabla: "  << result.first.second;
                cout << "\n" << "Broj koraka izvršavanja: " << result.second;
                cout << "\n" << "Broj operatora i literala u formuli: " <<tokens.second;
            }
            else {
                cout << "\nFormula unprovable\n";
            }
            cout << "\n\n";
        }
        if(postoji == false) {
             appendFileToWorkWith.close();
        }
    }
    catch(string e){
        cout << e;
    }
    catch(exception e) {
        cout << "Greska";
    }
return 0;
}

