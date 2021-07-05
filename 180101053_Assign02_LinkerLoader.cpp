/*

Run the commands in the folder contaning the code and the input file - inp_ass2.txt

TO COMPILE:
 g++ 180101053_Assign02_LinkerLoader.cpp

TO RUN:
 ./a.out

Following is the 2 pass linker loader

pass 1 gives the EStable.txt as output
pass2 gives the pass2_output_file.txt with the memory contents as output as shown in the book


*/

#include <iostream>
#include <fstream>
#include <cstring>
#include <cstdlib>
#include <iomanip>
#include <sstream>
#include <stdio.h>
#include <math.h>
#include <stdlib.h>
#include <string>
#include <map>
#include <utility>
#include <vector>
#include <iomanip>
using namespace std;

string name_of_input_asm;  		//stores the name of the input file containing the object code of various sections
int CSaDDR,PROGaDDR,EXECaDDR;	// control_section_address , program_address and execution address respectively;

long int neg = (long int)0xFFFFFFFF000000; //used as a borrow for doing negative calculatioins with hexadecimal numbers


ifstream input_file;

//file pointers to create outputs
ofstream pass1_output_file; //output of pass1 
ofstream pass2_output_file; //output of pass2

//struct to store the External Symbols and Control Sections in a table
struct es
{
	int address;
	int length;
	es()
	{
		address=0;
		length=0;
	}
	es(int addr,int len)
	{
		address=addr;
		length=len;

	}

};
vector<pair<string,es> > EStable;			//stores the external symbol table
vector<pair<int,string> > Memory_objcode;	//stores the memory content byte wise : address mapped to Memory_objcode

//searches the vector by name of external symbol name and return index if found else -1
int search_vector(vector<pair<string,es> > EStable,string name)
{
	for(int i=0;i<EStable.size();i++)
	{
		if(EStable[i].first==name)
		{
			return i;
		}
	}
	return -1;

}

//searches the vector by address of external symbol name and return index if found else -1
int search_vector2(vector<pair<int,string> > Memory_objcode,int addr)
{
	for(int i=0;i<Memory_objcode.size();i++)
	{
		if(Memory_objcode[i].first==addr)
		{
			return i;
		}
	}
	return -1;

} 

//converts integer to a minimum min_len digit hexadeicmal string
string to_hex_string(int dec_num,int min_len)
{
	string hexdec_num="";
    char hex[]={'0','1','2','3','4','5','6','7','8','9','A','B','C','D','E','F'};
    while(dec_num>0)
    {
        int r = dec_num % 16;
        hexdec_num = hex[r] + hexdec_num;
        dec_num = dec_num/16;
    }
    
    if(hexdec_num.length()<min_len)hexdec_num.insert(0,min_len-hexdec_num.length(),'0');
    //transform(res.begin(), res.end(), res.begin(), ::toupper);
    return hexdec_num;
}
string to_hex_string6(int i)
{
    stringstream ss;
    ss<<hex<<i;
    string res=ss.str();
    if(res.length()<6)res.insert(0,6-res.length(),'0');
    transform(res.begin(), res.end(), res.begin(), ::toupper);
    return res;
}

//convert hex string to decimal int
//hex_to_int
int stringhexToInt(string hex_string)
{
	int x;
	x=stoi(hex_string, 0, 16);
	return x;

}


void handle_D_records(vector<string> records)
{

	int no_of_es=records.size()-1;
	records[0]= records[0].substr(1); //remove D;
	
	string es_name=records[0];
	
	for(int i=0;i<no_of_es;i++) //for each symbol in the record do
	{
		string es_addr="";
		
		es_addr=records[i+1].substr(0,6);

		if(search_vector(EStable,es_name)>=0)
		{
			cout<<"ERROR : DUPLICATE EXTERNAL SYMBOL FOUND\n";
		}
		else
		{
			struct es new_es(stringhexToInt(es_addr) + CSaDDR,0);
			//insert the new external symbol in the table
			EStable.push_back(make_pair(es_name,new_es));
			//print to the table
			pass1_output_file<<"    \t\t"<<es_name<<" \t\t "<< to_hex_string(new_es.address,4)<<" \t\t \n";

		}

		if(i<no_of_es-1) //read the next name
		{
			es_name="";
			es_name=records[i+1].substr(6);
		
		}
		

	}
}
void handle_T_records(string records)
{
	string specified_addr="";
	
	specified_addr=records.substr(1,6);
	
	int location = CSaDDR + stringhexToInt(specified_addr);
	//here you have to put the record somehow
	for(int i=9;i<records.length();i+=2)
	{
		string temp=records.substr(i,2);
		//store the read record in the memory
		Memory_objcode.push_back(make_pair(location,temp));
		location++;

	}
}

string handle_modification(string old_val,string symbol_name,string op)
{
	int new_val=0;
	long int borrow=(long int)0xFFFFFFFF000000;
	if(old_val[0]=='F')
	{
		new_val=borrow; //used as a borrow for doing negative calculatioins with hexadecimal numbers

	}
	int inde=search_vector(EStable,symbol_name);

	//add or sub as per M record
	if(op.back()=='+')
	{
		new_val += stringhexToInt(old_val) + EStable[inde].second.address;
	}
	else
	{
		new_val +=  stringhexToInt(old_val) - EStable[inde].second.address ;
	} 

	string new_hex=to_hex_string6(new_val);

	if(new_hex.length()>6 && new_hex[0]=='F' && new_hex[1]=='F')
	{
		new_hex=new_hex.substr(2);
	}

	return new_hex;
}

void handle_M_records(string records)
{
	string symbol_name="";
	string sym_loc="";
	string sym_len="";

	for(int v=1;v<records.length();v++)
	{
		if(v<7)sym_loc+=records[v];
		else if(v<9)sym_len+=records[v];
		else if(v<10)sym_len+=records[v];
		else symbol_name+=records[v];
	}

	int g=stringhexToInt(sym_loc) + CSaDDR;


	string old_val="";
	//read the old value from the memory
	int ind[3];
	 ind[0]=search_vector2(Memory_objcode,g);
	ind[1]=search_vector2(Memory_objcode,g+1);
	 ind[2]=search_vector2(Memory_objcode,g+2);

	for(int v=0;v<3;v++)
	{
		if(ind[v]!=-1)old_val+=Memory_objcode[ind[v]].second;
		else old_val+="";

	}
	
	
	string str_hex=handle_modification(old_val,symbol_name,sym_len);


	int k=0;
	//store the new val in the memory
	for(int v=0;v<3;v++)
	{
		if(ind[v]==-1)
		{
			Memory_objcode.push_back(make_pair(g+v,""));
			Memory_objcode.back().second+=str_hex[k];
			Memory_objcode.back().second+=str_hex[k+1];

		}
		else 
		{
			Memory_objcode[ind[v]].second="";
			Memory_objcode[ind[v]].second+=str_hex[k];
			Memory_objcode[ind[v]].second+=str_hex[k+1];
		}
		k+=2;
	}

	
}

//converts a given line string to a vector of words seperated as per spaces
//extra spaces are skipped
vector<string> line_to_words(string str) 
{ 
    // Used to split string around spaces. 
    vector<string> res;
    istringstream ss(str); 

    string word; // for storing each word 
  
    // Traverse through all words 
    // while loop till we get  
    // strings to store in string word 
    while (ss >> word)  
    { 
    	res.push_back(word);
        //push the read word       
    } 
    return res;
} 

//pass 1 of the assembler to handle H and D records
void pass1()
{
	
	input_file.open(name_of_input_asm);

	//this file will contain the external symbol table as contructed after pass1;
	pass1_output_file.open("EStable.txt");
	pass1_output_file<<"C-section\tSYmbol Name  Address \t Length\n";

	
	CSaDDR=PROGaDDR; //assign starting address for relocation

	string current_secname=""; //stores the name of the current control section
	int cs_length=0;

	string line="";

	while(getline(input_file,line,'\n'))
	{
		vector<string> line_w=line_to_words(line);
		if(line_w[0][0]=='H')
		{
			string cs_len="",CSaDDR_obj="";
			CSaDDR_obj=line_w[1].substr(0,6);
			cs_len+=line_w[1].substr(6);

			line_w[0]=line_w[0].substr(1); //to remove H

			if(search_vector(EStable,line_w[0])>=0)
			{
				cout<<"ERROR : DUPLICATE SECTION FOUND\n";
			}
			else
			{
				//insert the control section in EStable;
				current_secname=line_w[0];
				es new_es (stringhexToInt(CSaDDR_obj) + CSaDDR,stringhexToInt(cs_len));
				EStable.push_back(make_pair(line_w[0],new_es));
				//print it to table
				pass1_output_file<<line_w[0]<<" \t\t  \t\t\t "<< to_hex_string(new_es.address,4) <<" \t\t "<< to_hex_string(new_es.length,4)<<" \t\t \n";

			}
			while(getline(input_file,line,'\n'))
			{
				vector<string> records=line_to_words(line);
				if(records[0][0]=='E') //end record
				{
					break;
				}
				if(records[0][0]=='D') //define records
				{
					handle_D_records(records);
					
				}
				
			}
			CSaDDR+=stringhexToInt(cs_len); //starting address for next section

		}

	}
	input_file.close();
	pass1_output_file.close();

}

//pass 2 of the loader to handle T and M records
void pass2()
{
	input_file.open(name_of_input_asm);
	CSaDDR=PROGaDDR;
	EXECaDDR=PROGaDDR;
	int cs_len;

	string current_secname="";
	string line="";

	//reading the input file again
	while(getline(input_file,line,'\n'))
	{
		vector<string> line_w=line_to_words(line);
		if(line_w[0][0]=='H') //header record indicate start of new control section
		{
			line_w[0]=line_w[0].substr(1);
			current_secname=line_w[0];
			int index=search_vector(EStable,current_secname);
			cs_len=EStable[index].second.length;


			while(getline(input_file,line,'\n'))
			{
				vector<string> records=line_to_words(line);
				if(records[0][0]=='E') //end of section
				{
					break;
				}

				if(records[0][0]=='T') //text record
				{
					
					handle_T_records(records[0]);

				}
				if(records[0][0]=='M') //modification record
				{
					
					handle_M_records(records[0]);
				}
			}
			if(line[0]=='E' && line.length()>1) //if address specified in the END record then make exec addr that + CSaDDR
			{
				line=line.substr(1);
				EXECaDDR = CSaDDR + stringhexToInt(line);
			}
			CSaDDR +=cs_len; // go to next section



		}

		//jump to location exec addr

	}
	input_file.close();

}

//help with the display of memory map
void printer_help(int col,char ch)
{
	for(int i=0;i<2;i++)
	{
		pass2_output_file<<ch;
	}
	if((col)%4==0)
	{
		pass2_output_file<<"\t";
	}
}

//printing the memory map
//16 bytes at a time for better readability

void obj_print()
{
	
	pass2_output_file.open("pass2_output_file.txt");

	pass2_output_file<<"Memory address _________________Contents______________________\n";
	int addr_final =(*Memory_objcode.rbegin()).first;
	
	int addr_counter=PROGaDDR - 16;

	for(int i=0; ;i++)
	{
		int indes=0;

		if(addr_counter > addr_final)
		{
			while((PROGaDDR-addr_counter)%16!=0)
			{
				printer_help(i+1,'x');
				i++;
				addr_counter++;
			}
			break;
		}
		if(i%16==0)
		{
			pass2_output_file<<to_hex_string(addr_counter,4)<<" \t ";
		}

		if(addr_counter<PROGaDDR)
		{
			printer_help(i+1,'x');
		}
		else if((indes=search_vector2(Memory_objcode,addr_counter))>=0 && Memory_objcode[indes].second!="")
		{

			pass2_output_file<<Memory_objcode[indes].second;
			if((i+1)%4==0)
				pass2_output_file<<" \t";		
		}
		else
		{
			printer_help(i+1,'.');
		}

		if((i+1)%16==0)pass2_output_file<<"\n";
		addr_counter++;

	}
	pass2_output_file.close();


}


int main()
{
	EStable.clear();
	name_of_input_asm="inp_ass2.txt";
	string pa;
	pa="4000"; //starting address usually received from the os
	PROGaDDR=stringhexToInt(pa);

	pass1();
	cout<<"pass1 done.finished creating es table in EStable.txt\n";
	pass2();
	cout<<"pass2 done.finished creating memory table in pass2_output_file.txt\n";
	obj_print();

	cout<<"Addr Objectcode\n";
	for(int i=0;i<Memory_objcode.size();i++)
		cout<<to_hex_string(Memory_objcode[i].first,4)<<" "<<Memory_objcode[i].second<<"\n";



}
