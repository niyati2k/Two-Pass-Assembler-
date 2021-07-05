/*

Run the commands in the folder contaniing the code and the input file - test_input.txt

TO COMPILE:
 g++ 180101053_Assign02_Assembler.cpp

TO RUN:
 ./a.out

Following is the assembler for sic xe with provisions for the extended version instructions in the code
pass1 creates the intermediate file
pass2 creates the listing.txt and output.obj

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

//structures are defined to create tables of location,symbols,ext,literals
struct loctab{
    string section_name;
    int loc;
    int start_addr;
    int length;
};
struct symtab{
	string symbol;
	int addr;
	bool type;
	int control_section;
};
struct ext{
    string symbol;
    int control_section;
    bool type;
};
struct littab{
	string name;
	int operand_value;
	int length;
	int addr;
};

//tables of register and optable defined in the machine code are stoerd in these maps
map<string,int> reg;
map<string,string> optab;
string buffer,operand,opcode,label;
int buf_i, curr_section, lineLength, line_num, loc,line_objectCode,line_opcode,line_index,line_addr,record_index,define_index,part_index,refer_index,modi_index;

//variables for formatting the output object codes as per various formats fo rhte six xe architechture
/*
two type of addressing modes
first:- |_op -6___|n|i|x|b|p|e|_____disp-12___| - n at 17 th location
second:- |_op -6___|n|i|x|b|p|e|_____disp-20__________| - n at 25 th location
for these we need to initiate the addresses prior so we can use directly
*/
static int format3_n=1<<17,format3_i=1<<16,format3_x=1<<15,format3_b=1<<14,format3_p=1<<13,format3_e=1<<12;
static int format4_n=1<<25,format4_i=1<<24,format4_x=1<<23,format4_b=1<<22,format4_p=1<<21,format4_e=1<<20;
static int BUFFER_SIZE = 256, OPTAB_LENGTH=28, REG_LENGTH=7;

//utilitiy variables to help in execution of the program
int OPTAB_INDEX,SYMTAB_INDEX, SYMTAB_COUNT, SYMTAB_FOUND, OPTAB_FOUND,LOCTAB_COUNT,LOCTAB_FOUND,LOCTAB_INDEX,LITTAB_COUNT,LITTAB_FOUND,LITTAB_INDEX,EXT_FOUND,EXT_INDEX,EXT_COUNT,REG_FOUND,REG_INDEX;
bool is_extended_format, is_literal;
int format3_neg = (1<<12) - 1, format4_neg=(1<<20) -1;

//vectors store the tables formed after pass1 and pass2
vector<loctab> LOCTAB(10); //loc for each csection
vector<symtab> SYMTAB(20); //symbol table
vector<ext> EXT(20);        //for D and R records due to EXTDEF AND EXTREF
vector<littab> LITTAB(20); //literal table

//initialising the machine codes available
void insertValuesOptab(){
	optab["LDA"]="00";
	optab["LDX"]="04";
	optab["LDL"]="08";
	optab["LDB"]="68";
	optab["LDT"]="74";
	optab["STA"]="0C";
	optab["STX"]="10";
	optab["STL"]="14";
	optab["LDCH"]="50";
	optab["STCH"]="54";
	optab["ADD"]="18";
	optab["SUB"]="1C";
	optab["MUL"]="20";
	optab["DIV"]="24";
	optab["COMP"]="28";
	optab["COMPR"]="A0";
	optab["CLEAR"]="B4";
	optab["J"]="3C";
	optab["JLT"]="38";
	optab["JEQ"]="30";
	optab["JGT"]="34";
	optab["JSUB"]="48";
	optab["RSUB"]="4C";
	optab["TIX"]="2C";
	optab["TIXR"]="B8";
	optab["TD"]="E0";
	optab["RD"]="D8";
	optab["WD"]="DC";
}

//clearing all global variables at the start of the program
void initialize(){
    operand="";label="";opcode="";buffer="";
	buf_i=line_num=lineLength=SYMTAB_COUNT=LOCTAB_COUNT=LITTAB_COUNT=EXT_COUNT=0;
	OPTAB_INDEX=SYMTAB_INDEX=LOCTAB_INDEX=LITTAB_FOUND=LITTAB_INDEX=EXT_FOUND=EXT_INDEX=REG_INDEX=-1;
    SYMTAB_FOUND=OPTAB_FOUND=LOCTAB_FOUND=REG_FOUND=0;
	is_extended_format=is_literal=false;
}

//help in reading a line from file and storing the read label opcode and operand
int readLine(fstream &fptr){
    buffer="";
    getline(fptr,buffer);
    buffer+='\n';
    lineLength = buffer.length();
	buf_i=0;
    //Read Label
    label="";
	while(buffer[buf_i] != ' ' && buffer[buf_i] !='\t' && buffer[buf_i] !='\n'){
		label += buffer[buf_i++];
	}
    
    //Skip spaces
    while(buffer[buf_i] == ' ' || buffer[buf_i] == '\t'){
		buf_i++;
	}
    //Read Opcode
    opcode="";
    while(buffer[buf_i] != ' ' && buffer[buf_i] !='\t' && buffer[buf_i] !='\n'){
		opcode += buffer[buf_i++];
	}
   
    //Skip spaces
    while(buffer[buf_i] == ' ' || buffer[buf_i] == '\t'){
		buf_i++;
	}
    //Read Operand
    operand="";
	while(buffer[buf_i] != ' ' && buffer[buf_i] !='\t' && buffer[buf_i] !='\n'){
		operand += buffer[buf_i++];
	}
    line_num++;
    return lineLength;
}

//converting the string to hexinteger
int stringToHex(string str){
    int ans=0;
    for(int i=0;i<str.length();i++){
        if('0'<=str[i] && str[i]<='9'){
            ans = ans*16 + (int)(str[i]-'0');
        }
        else if('a' <= str[i] && str[i]<= 'f'){
            ans = ans*16 + (int)(10 + (str[i]-'a') );
        }
        else if('A' <= str[i] && str[i]<= 'F'){
            ans = ans*16 + (int)(10 + (str[i]-'A'));
        }
    }
    return ans;
}

//calculate the value of expression as per the refrences 
void calculate_expr(string str, int *val, bool *expr_type, bool *ref_involved){
    string tmp="";
    bool found=false;
    *expr_type=false;
    int cnt_rel=0;
    int i=0;
    if(str=="*"){
        *val=LOCTAB[curr_section].loc;
        cnt_rel++;
    }
    else{
        int prev_sign=1;
        while(i<str.length()){
            if(str[i]=='-'|| str[i]=='+'){
                found=false;
                for(int k=0;k<SYMTAB_COUNT;k++){
                    if(SYMTAB[k].symbol==tmp){
                        if(SYMTAB[k].control_section !=curr_section){
                            *ref_involved = true;
                            return;
                        }
						*val += prev_sign*SYMTAB[k].addr;
						found = true;
						cnt_rel += prev_sign;
						break; 
                    }
                }
                tmp="";
                if(str[i]=='-'){
					prev_sign = -1;
				}
				else{
					prev_sign = 1;
				}
            }
            else{
                tmp+=str[i];
            }
            i++;
        }
        found=false;
        for(int k=0;k<SYMTAB_COUNT;k++){
            if(SYMTAB[k].symbol==tmp){
                if(SYMTAB[k].control_section!=curr_section){
                    *ref_involved=true;
                    return;
                }
                *val+=prev_sign*SYMTAB[k].addr;
                found=true;
                cnt_rel+=prev_sign;
                break;
            }
        }
    }
    if(cnt_rel==0){
		*expr_type = true;
	}
	*ref_involved = false;
}

//used to search the sym table usign symbol name
void search_SYMTAB(string str){
    SYMTAB_INDEX=-1;
    SYMTAB_FOUND=0;
	for(int i=0;i<SYMTAB_COUNT;i++){
		if(SYMTAB[i].symbol==str && SYMTAB[i].control_section==curr_section){
			SYMTAB_FOUND=1;
			SYMTAB_INDEX=i;
			break;
		}
	}
}

//inserting new symbol in the table
void add_SYMTAB(string str){
    SYMTAB_FOUND=0;
    SYMTAB[SYMTAB_COUNT].symbol=str;
    SYMTAB[SYMTAB_COUNT].addr = LOCTAB[curr_section].loc;
    SYMTAB_INDEX = SYMTAB_COUNT;
    SYMTAB[SYMTAB_INDEX].type=0;
    SYMTAB[SYMTAB_INDEX].control_section=curr_section;
    SYMTAB_COUNT++;
}

//used to calculate value of literal for resw resb type instructions
int valOfLiteral(string str){
    int val=0;
    string tmp_ptr="";
    if((str[0]=='C'||str[0]=='c')&& str[1]=='\''){
        for (int i = 2; i<=str.length()-2; i++){
			val += (int)str[i];
			val<<=8;
		}
		val>>=8;
    }
    else if( (str[0]=='X' || str[0]=='x' ) && str[1]=='\''){
		for(int i=2;i<=str.length()-2;i++ ){
			tmp_ptr+=str[i];
		}
		val += stringToHex(tmp_ptr);
	}
	return val;
}

//used to calculate length of literal for constants type instructions to add to the location counter of the section
int lenOfConstant(string str){
	string tmp;
	int i=0;
	tmp=str;
	if ( (tmp[0] =='C' || tmp[0] =='c') && tmp[1] =='\''){
		for (i = 2; i<=tmp.length(); i++){
			if (tmp[i] == '\''){
				i -=2;
				break;
			}
		}
	}
	if ((tmp[0] =='X' || tmp[0] =='x') && tmp[1] =='\''){
		i = 1;
	}
	return i;
}

//used to search the literal table vector defined
void search_LITTAB(string str){
    LITTAB_INDEX=-1;
    LITTAB_FOUND=0;
	for(int i=0;i<LITTAB_COUNT;i++){
		if(LITTAB[i].name==str){
			LITTAB_FOUND=1;
			LITTAB_INDEX=i;
			break;
		}
	}
}

//inseerting the new literals
void add_LIITAB(string str){
    LITTAB[LITTAB_COUNT].name=str;
    LITTAB_INDEX = LITTAB_COUNT;
    LITTAB[LITTAB_COUNT].operand_value = valOfLiteral(str.substr(1));
    LITTAB[LITTAB_COUNT].addr = -1;
    LITTAB[LITTAB_COUNT].length = lenOfConstant(str.substr(1));
    LITTAB_FOUND=0;
    LITTAB_COUNT++;
}

//search the ext table for def or r record as per the is_extdef vairable
void search_EXT(string str1, bool is_extdef){
    string str="";
    str=str1;
    EXT_FOUND=0;
    EXT_INDEX=-1;
    string token="";
    istringstream iss(str);
    while(getline(iss,token,',')){
        for(int i=0;i<EXT_COUNT;i++){
            if(EXT[i].symbol==token && EXT[i].control_section==curr_section){
                EXT_FOUND=1;
                EXT_INDEX = i;
                break;
            }
        }
        if(EXT_FOUND!=1){
            EXT[EXT_COUNT].symbol=token;
            EXT[EXT_COUNT].control_section = curr_section;
            EXT[EXT_COUNT].type = is_extdef;
            EXT_INDEX = EXT_COUNT;
            EXT_COUNT++;
        }
    }
}


//When ORG is encountered, the assembler resets its LOCCTR to the specified value
//For each literal with empty address field, assign the address and update the LOC of curr section accordingly
void handle_LTORG(fstream &fptr){
    for(int i=0;i<LITTAB_COUNT;i++){
		if(LITTAB[i].addr == -1){
            LITTAB[i].addr = LOCTAB[curr_section].loc;
            fptr<<setfill('0')<<setw(4)<<right<<uppercase<<hex<<LOCTAB[curr_section].loc<<"\t"<<"*\t\t ";
            fptr<<setfill(' ')<<setw(8)<<left<<LITTAB[i].name<<"\n";
            LOCTAB[curr_section].loc += lenOfConstant(LITTAB[i].name.substr(1));
		}
	}
}

//increasing location counter as per the pseudo code for various instructions
void increase_loc(int& n){
	if(OPTAB_FOUND && (opcode=="COMPR" || opcode=="CLEAR" || opcode=="TIXR" )){
		n +=2;
	}
    else if(OPTAB_FOUND && !is_extended_format){
        n +=3;
	}
	else if(OPTAB_FOUND && is_extended_format){
		n +=4;
	}
	else if(opcode=="WORD"){
		n += 3;
	}
	else if(opcode=="RESW"){
		n += 3*stoi(operand);
	}
	else if(opcode=="RESB"){
		n += stoi(operand);
	}
	else if(opcode=="BYTE"){
		n += lenOfConstant(operand);
	}
}

//clearing the variables for usign them in pass2;
void resetForPass2(){
    buffer=operand=opcode=label="";
    buf_i=line_num=lineLength=curr_section=0;
	OPTAB_INDEX=SYMTAB_INDEX=LOCTAB_INDEX=LITTAB_INDEX=REG_FOUND=REG_INDEX= -1;
    OPTAB_FOUND=LOCTAB_FOUND=SYMTAB_FOUND=LITTAB_FOUND=0;
	is_extended_format=is_literal=false;
}

//breaking a line from the intermediate file into the address label opcode and operand
int readLinePass2(fstream &fptr){
    buffer="";
    getline(fptr,buffer);
    buffer+='\n';
    lineLength = buffer.length();
	buf_i=0;
    //Read LOCCTR
    string tmp="";
    while(buffer[buf_i] != ' ' && buffer[buf_i] !='\t' && buffer[buf_i] !='\n'){
		tmp += buffer[buf_i++];
	}
    loc= stringToHex(tmp);
    buf_i+=1;
    //Read Label
    label="";
	while(buffer[buf_i] != ' ' && buffer[buf_i] !='\t' && buffer[buf_i] !='\n'){
		label += buffer[buf_i++];
	}
    //Skip spaces
    while(buffer[buf_i] == ' ' || buffer[buf_i] == '\t'){
		buf_i++;
	}
    //Read Opcode
    opcode="";
    while(buffer[buf_i] != ' ' && buffer[buf_i] !='\t' && buffer[buf_i] !='\n'){
		opcode += buffer[buf_i++];
	}
    //Skip spaces
    while(buffer[buf_i] == ' ' || buffer[buf_i] == '\t'){
		buf_i++;
	}
    //Read Operand
    operand="";
	while(buffer[buf_i] != ' ' && buffer[buf_i] !='\t' && buffer[buf_i] !='\n'){
		operand += buffer[buf_i++];
	}
    return lineLength;
}

//insert values in the register table map
void insertValuesReg(){
    reg["A"]=0;
    reg["X"]=1;
    reg["L"]=2;
    reg["B"]=3;
    reg["S"]=4;
    reg["T"]=5;
    reg["F"]=6;
}

//finding the format type from sic xe for creating the object code as per instructions
int format_type(string opc){
    if(opc=="CLEAR"||opc=="COMPR"||opc=="TIXR"){
        return 2;
    }
    else if(opc[0]=='+'){
        return 4;
    }
    else{
        if(optab.find(opc)!=optab.end()){
            return 3;
        }
    }
    return 0;
}

//searching the loc table using the names of the sections
void search_LOCTAB(string str){
    LOCTAB_INDEX=-1;
	for(int i=0;i<LOCTAB_COUNT;i++){
		if(LOCTAB[i].section_name==str){
			LOCTAB_FOUND=1;
			LOCTAB_INDEX=i;
			break;
		}
	}
}

//copy the modification records from the modified.txt file and put them into the output.obj at the end of the other records
void copy_modification_records(string &modi_record, fstream &modi, fstream &output){
    modi_record="";
    modi_index=0;
    modi.close();
    modi.open("modified.txt",ios::in);
    if(!modi.is_open()){
        cout<<"Can't open modified.txt"<<endl;
        return;
    }
    while(getline(modi,modi_record)){
        output<<modi_record<<"\n";
    }
    modi_record="";
    modi_index=0;
    modi.close();
    modi.open("modified.txt",ios::out);
}

//creating the modification records adn printing them out to modified.txt to hold them
 //  generate modification record
//Each time the assembler produces an instruction with an address, a
//modification record (or M-record) is produced
void generate_modification_record(string &modi_record,string &str, fstream &modi){
    modi_record=""; //stores the Mrecords
    modi_index=0;
    int prev_sign=1,i=0;
    string tmp;
    char buff[200];  
    bool found=false;
    while(i<str.length()){
        if(str[i]=='-'||str[i]=='+'){
            found=false;
            for(int k=0;k<SYMTAB_COUNT;k++){
                if(SYMTAB[k].symbol==tmp){
                    if(SYMTAB[k].control_section!=curr_section){
                        modi_record="";
                        modi_index = sprintf(buff,"M%06X06",loc); //printing hexadecinal address to buff
                        modi_record+=buff;
                        if(prev_sign==1){   //print operator
                            modi_index+=1;
                            modi_record+='+';
                        }
                        else{
                            modi_index+=1;
                            modi_record+='-';
                        }
                        char c[200];
                        int u;
                        for(u=0;u<SYMTAB[k].symbol.length();u++){
                            c[u]=SYMTAB[k].symbol[u];
                        }
                        c[u]='\0';
                        modi_index+=sprintf(buff,"%s",c); //name of symbol
                        modi_record+=buff;
                        modi<<modi_record<<"\n";
                    }
                }
            }
            tmp="";
            if(str[i]=='-'){
                prev_sign=-1;
            }
            else {
                prev_sign=1;
            }
        }
        else{
            tmp+=str[i];
        }
        i++;
        
    }
    found=false;
    for(int k=0;k<SYMTAB_COUNT;k++){
        if(SYMTAB[k].symbol==tmp){
            if(SYMTAB[k].control_section!=curr_section){
                modi_record="";
                modi_index = sprintf(buff,"M%06X06",loc);
                modi_record+=buff; //adding the opreator + or -
                if(prev_sign==1){
                    modi_index+=1;
                    modi_record+='+';
                }
                else{
                    modi_index+=1;
                    modi_record+='-';
                }
                char c[200];
                int u;
                for(u=0;u<SYMTAB[k].symbol.length();u++){
                    c[u]=SYMTAB[k].symbol[u];
                }
                c[u]='\0';
                modi_index+=sprintf(buff,"%s",c); //printing the name of the symbol
                modi_record+=buff;
                modi<<modi_record<<"\n";
            }
        }
    }
    
}

//pass1 of the assembler for sic xe
void pass1(){
    cout<<"Pass-1 is running"<<endl;
    string tmp_opcode;
    fstream input, intermediate;
	input.open("test_input.txt",ios::in);
    if(!input.is_open()){
		printf("Cannot open test_input.txt\n");
		exit(1);
	}
	intermediate.open("intermediate.txt",ios::out);
	if(!intermediate.is_open()){
		printf("Cannot open intermediate.txt\n");
		exit(1);
	}
    readLine(input);
    if(opcode=="START"){
        LOCTAB[curr_section].start_addr = stringToHex(operand);
		LOCTAB[curr_section].loc = LOCTAB[curr_section].start_addr;
		LOCTAB[curr_section].section_name=label;
		LOCTAB_COUNT++;
        intermediate<<setfill('0')<<setw(4)<<right<<uppercase<<hex<<LOCTAB[curr_section].loc<<"\t";
        intermediate<<setfill(' ')<<setw(8)<<left<<label<<" "<<setw(8)<<left<<opcode<<" "<<setw(8)<<left<<operand<<"\n";
		readLine(input);
	}
	else{
		LOCTAB[curr_section].start_addr=LOCTAB[curr_section].loc=0;
	}
    while(opcode!="END"){
        //if comment line then directly to the intermediate file
        if(buffer[0]=='.'||buffer[0]=='\n'){
            intermediate<<buffer;
        }
        else{ //handle all operations required :
            if(opcode=="EQU"){
                int val=0;
				bool expr_type=false;
				bool ref_involved = false;
                calculate_expr(operand, &val, &expr_type, &ref_involved); //calculate the operand
                // search the SYMTAB for the label and add if not present
                search_SYMTAB(label);
                if(!SYMTAB_FOUND){
                    add_SYMTAB(label);
                }
                SYMTAB[SYMTAB_INDEX].addr = val; // assign the value of operand
				SYMTAB[SYMTAB_INDEX].type = expr_type; // assign the type of expression
                intermediate<<setfill('0')<<setw(4)<<right<<hex<<val<<"\t";
                intermediate<<setfill(' ')<<setw(8)<<left<<label<<" "<<setw(8)<<left<<opcode<<" "<<setw(8)<<left<<operand<<"\n";
            }
            else if(opcode=="CSECT"){
                LOCTAB[curr_section].length = LOCTAB[curr_section].loc - LOCTAB[curr_section].start_addr;
				LOCTAB[LOCTAB_COUNT].section_name=label;
				LOCTAB[LOCTAB_COUNT].loc=LOCTAB[LOCTAB_COUNT].start_addr=0;
				curr_section = LOCTAB_COUNT;
				LOCTAB_COUNT++;
				intermediate<<setfill('0')<<setw(4)<<right<<uppercase<<hex<<LOCTAB[curr_section].loc<<"\t";
                intermediate<<setfill(' ')<<setw(8)<<left<<label<<" "<<setw(8)<<left<<opcode<<" "<<setw(8)<<left<<operand<<"\n";
            }
            else{
                if(label!=""){ //if there is a symbol in label
                    search_SYMTAB(label); // search for symbol in SYMTAB and if not present then add
					if(SYMTAB_FOUND==0){
                        add_SYMTAB(label);
                    }
                }
                if(opcode[0]=='+'){
                    is_extended_format=true;
                    tmp_opcode=opcode.substr(1);
                }
                else{
					is_extended_format = false;
					tmp_opcode=opcode;
				}
                if(optab.find(tmp_opcode)==optab.end()) { //checking if theopcode exists in the table
                    OPTAB_FOUND=0;
                }
                else{
                    OPTAB_FOUND=1;
                }
                is_literal=false;
                if(operand[0]=='='){//literal
                    is_literal=true;
                    search_LITTAB(operand); // find the literal, if not present add a entry
					if(LITTAB_FOUND==0){
                        add_LIITAB(operand);
					}
                }
                if(opcode=="EXTDEF" || opcode=="EXTREF"){
                    if(opcode=="EXTDEF"){
                        search_EXT(operand, true);
                    }
                    else{
                        search_EXT(operand, false);
                    }
                    intermediate<<"\t\t"<<setfill(' ')<<setw(8)<<left<<label<<" "<<setw(8)<<left<<opcode<<" "<<setw(8)<<left<<operand<<"\n";
				}
                else if(opcode=="LTORG"){
					intermediate<<"\t\t"<<setfill(' ')<<setw(8)<<left<<label<<" "<<setw(8)<<left<<opcode<<" "<<setw(8)<<left<<operand<<"\n";
					handle_LTORG(intermediate);
				}
				else{
					intermediate<<setfill('0')<<setw(4)<<right<<uppercase<<hex<<LOCTAB[curr_section].loc<<"\t";
                    intermediate<<setfill(' ')<<setw(8)<<left<<label<<" "<<setw(8)<<left<<opcode<<" "<<setw(8)<<left<<operand<<"\n";
				}
            }
            increase_loc(LOCTAB[curr_section].loc); // increase Location counter
        }
        readLine(input); //read next line
    }
    intermediate<<"\t\t"<<setfill(' ')<<setw(8)<<left<<label<<" "<<setw(8)<<left<<opcode<<" "<<setw(8)<<left<<operand<<"\n";// last line
	handle_LTORG(intermediate); //handle ltorg lines finally 
	LOCTAB[curr_section].length = LOCTAB[curr_section].loc - LOCTAB[curr_section].start_addr; //calc the length of the code 
	cout<<"Pass-1 completed\n";
	cout<<"Number of lines read: "<<line_num<<endl;
    input.close();
    intermediate.close();
}

//pass2 of the assembler for sic xe
//creates listing file by appending the calculated object code to the end of the intermeidiate file 
//creates the output.obj which was H,T,R,D,M records for the given asm code
//modified.txt is empty at the end of pass2
void pass2(){
    string record,part,object_code,define_record,refer_record;
    string modi_record,tmp_opcode,tmp_operand;
    record=object_code=define_record=refer_record=modi_record=tmp_opcode=tmp_operand="";
    int line_objectCode=line_opcode=line_index=line_addr=record_index=part_index=define_index=refer_index=modi_index=0;
    cout<<"Pass-2 started\n";
    fstream intermediate,output,listing,modi;

    //read from the file created in pass1
    intermediate.open("intermediate.txt",ios::in);

    //creating the three output files. modified.txt is empty at the end as it is copied to the output file
    listing.open("listing.txt",ios::out);
    output.open("output.obj",ios::out);
    modi.open("modified.txt",ios::out);
    if(!intermediate.is_open()){
        printf("Cannot open intermediate.txt\n");
        exit(1);
    }
    if(!output.is_open()){
        printf("Cannot open output.obj\n");
        exit(1);
    }
    if(!listing.is_open()){
        printf("Cannot open listing.txt\n");
        exit(1);
    }
    if(!modi.is_open()){
        printf("Cannot open modified.txt\n");
        exit(1);
    }
    readLinePass2(intermediate);
    if(opcode=="START"){
        listing<<setfill('0')<<setw(4)<<right<<uppercase<<hex<<loc<<"\t";
        listing<<setfill(' ')<<setw(8)<<left<<label<<" "<<setw(8)<<left<<opcode<<" "<<setw(8)<<left<<operand<<"\n";
        readLinePass2(intermediate);
    }
    output<<"H"<<setfill(' ')<<setw(6)<<left<<LOCTAB[curr_section].section_name;
    output<<setfill('0')<<setw(6)<<right<<uppercase<<hex<<LOCTAB[curr_section].start_addr;
    output<<setfill('0')<<setw(6)<<right<<uppercase<<hex<<LOCTAB[curr_section].length<<"\n";
    char buff[100];
    record_index+=sprintf(buff,"%s","T");
    record+=buff;
    record_index+=sprintf(buff,"%06X",loc);
    record+=buff;
    int start_loc = loc;
    while(opcode!="END"){
        line_objectCode=0;
        line_opcode=0;
        line_index=0;
        OPTAB_FOUND=0;
        SYMTAB_FOUND=0;
        LITTAB_FOUND=0;
        object_code="";
        tmp_opcode=opcode;
        tmp_operand=operand;

        //if commented line then directly print into the listing file
        if(buffer[0]=='.'||buffer[0]=='\n'){
            listing<<buffer;
        }
        else{
            if(label=="*"){ //creating the opcode as per diff formats of opcode
                search_LITTAB(opcode);
                if(LITTAB_FOUND){
                    line_objectCode=LITTAB[LITTAB_INDEX].operand_value;
                }
                sprintf(buff,"%X",line_objectCode);
                object_code=buff;
                listing<<setfill('0')<<setw(4)<<right<<uppercase<<hex<<loc<<"\t";
                listing<<setfill(' ')<<setw(8)<<left<<label<<" "<<setw(8)<<left<<opcode<<" "<<setw(32)<<left<<operand<<"\t";
                listing<<uppercase<<hex<<line_objectCode<<"\n";
            }
            else if(format_type(opcode)==2){
                if(optab.find(opcode)!=optab.end()){
                    OPTAB_FOUND=1;
                }
                line_objectCode=stringToHex(optab[opcode]);
                line_objectCode <<=8;
                string r1,r2;
                r1=operand.substr(0,1);
                line_objectCode+= (reg[r1]<<4);
                if(operand[1]==','){
                    r2=operand.substr(2,1);
                    line_objectCode+=reg[r2];
                }
                sprintf(buff,"%04X",line_objectCode);
                object_code=buff;
                listing<<setfill('0')<<setw(4)<<right<<uppercase<<hex<<loc<<"\t";
                listing<<setfill(' ')<<setw(8)<<left<<label<<" "<<setw(8)<<left<<opcode<<" "<<setw(32)<<left<<operand<<"\t";
                listing<<setfill('0')<<setw(4)<<right<<uppercase<<hex<<line_objectCode<<"\n";
            }
            else if(format_type(opcode)==3){
                if(optab.find(opcode)!=optab.end()){
                    OPTAB_FOUND=1;
                }
                line_objectCode=stringToHex(optab[opcode]);
                line_objectCode <<=16;
                
                if(operand!=""){
                    if(operand[0]=='#'){ // Immediate
                        search_SYMTAB(operand.substr(1));
                        if(SYMTAB_FOUND){ // OP #m
                            line_objectCode += SYMTAB[SYMTAB_INDEX].addr - (loc+3) + format3_i + format3_p;
                        }
                        else{ // OP #c
                            line_objectCode += stringToHex(operand.substr(1)) + format3_i;
                        }
                    }
                    else if(operand[0]=='@'){ // Indirect
                        search_SYMTAB(operand.substr(1));
                        if(SYMTAB_FOUND){ // OP @m
                            line_index = (SYMTAB[SYMTAB_INDEX].addr-(loc+3));
                            line_index  = line_index & format3_neg;
                            line_objectCode += line_index + format3_p + format3_n;
                        }
                        else{
                             // OP @c
                             line_objectCode += stringToHex(operand.substr(1)) + format3_n;
                        }
                    }
                    else if(operand[0]=='='){
                        search_LITTAB(operand);
                        if(LITTAB_FOUND){
                                line_index = LITTAB[LITTAB_INDEX].addr - (loc+3);
                                line_index = line_index & format3_neg;
                            line_objectCode += line_index;
                        }
                        line_objectCode += format3_p + format3_n + format3_i;
                    }
                    else if(operand[operand.length()-1]=='X' && operand[operand.length()-2]==','){ // OP m,X
                        line_objectCode += format3_n + format3_i + format3_x + format3_p;
                        operand[operand.length()-2]='\0';
                        search_SYMTAB(opcode);
                        if(SYMTAB_FOUND){
                            line_index = (SYMTAB[SYMTAB_INDEX].addr-(loc+3));
                            line_index  = line_index & format3_neg;
                            line_objectCode+= line_index;
                        }
                    }
                    else{ // simple
                        search_SYMTAB(operand);
                        line_objectCode += format3_p + format3_n + format3_i;
                        if(SYMTAB_FOUND){ // OP m
                            line_index = (SYMTAB[SYMTAB_INDEX].addr-(loc+3));
                            line_index  = line_index & format3_neg;
                            line_objectCode+= line_index;
                        }
                    }


                }
                else{
                    line_objectCode += format3_i + format3_n;
                }
                sprintf(buff,"%06X",line_objectCode);
                object_code=buff;
                listing<<setfill('0')<<setw(4)<<right<<uppercase<<hex<<loc<<"\t";
                listing<<setfill(' ')<<setw(8)<<left<<label<<" "<<setw(8)<<left<<tmp_opcode<<" "<<setw(32)<<left<<tmp_operand<<"\t";
                listing<<setfill('0')<<setw(6)<<right<<uppercase<<hex<<line_objectCode<<"\n";
            }
            else if(format_type(opcode)==4){
                modi_index=sprintf(buff,"M%06X05+",loc+1);
                modi_record=buff;
                if(optab.find(opcode.substr(1))!=optab.end()){
                    OPTAB_FOUND=1;
                }
                line_objectCode=stringToHex(optab[opcode.substr(1)]);
                line_objectCode <<=24;
                line_objectCode +=format4_n + format4_i + format4_e;
                if(operand!=""){
                    if(operand[operand.length()-1]=='X' && operand[operand.length()-2]==','){ // +OP m,X
                        line_objectCode += format4_x;
                        operand[operand.length()-2]='\0';
                        search_SYMTAB(opcode);
                        char c[200];
                        for(int i=0;i<operand.length();i++){
                            c[i]=operand[i];
                        }
                        c[operand.length()]='\0';
                        modi_index += sprintf(buff,"%-6s",c);
                        modi_record+=buff;
                        if(SYMTAB_FOUND){
                            line_index = (SYMTAB[SYMTAB_INDEX].addr-(loc+3));
                            line_index  = line_index & format3_neg;
                            line_objectCode+= line_index;
                        }
                    }
                    else{
                        search_SYMTAB(operand);
                        char c[200];
                        for(int i=0;i<operand.length();i++){
                            c[i]=operand[i];
                        }
                        c[operand.length()]='\0';
                        modi_index += sprintf(buff,"%-6s",c);
                        modi_record+=buff;
                        if(SYMTAB_FOUND){
                            line_index += SYMTAB[SYMTAB_INDEX].addr;
                        }
                        else{
                            for(int i=0;i<EXT_COUNT;i++){
                                if(EXT[i].symbol==operand && EXT[i].control_section == curr_section){
                                    line_index=0;
                                }
                            }
                        }
                    }
                    modi<<modi_record<<"\n";
                    
                }
                line_index &= format4_neg;
                    line_objectCode += line_index;
                    sprintf(buff,"%08X",line_objectCode);
                    object_code=buff;
                    listing<<setfill('0')<<setw(4)<<right<<uppercase<<hex<<loc<<"\t";
                    listing<<setfill(' ')<<setw(8)<<left<<label<<" "<<setw(8)<<left<<tmp_opcode<<" "<<setw(32)<<left<<tmp_operand<<"\t";
                    listing<<setfill('0')<<setw(8)<<right<<uppercase<<hex<<line_objectCode<<"\n";
            }
            else if(opcode=="CSECT"){ //start of a new section we print E and modification records 
                search_LOCTAB(label);
                if(LOCTAB_FOUND){
                    record_index+=sprintf(buff,"%02X",(int)(part.length()/2));
                    record+=buff;
                    char c[200];
                    for(int i=0;i<part.length();i++){
                        c[i]=part[i];
                    }
                    c[part.length()]='\0';
                    record_index += sprintf(buff,"%-6s",c);
                    record+=buff;
                    if(part!=""){
                        output<<record<<"\n";
                    }
                    copy_modification_records(modi_record,modi,output);
                    if(curr_section==0){
                        output<<"E"<<setfill('0')<<setw(6)<<right<<uppercase<<hex<<LOCTAB[curr_section].start_addr<<"\n\n";
                    }
                    else{
                        output<<"E\n\n";
                    }
                    listing<<setfill('0')<<setw(4)<<right<<uppercase<<hex<<loc<<"\t";
                    listing<<setfill(' ')<<setw(8)<<left<<label<<" "<<setw(8)<<left<<opcode<<" "<<setw(8)<<left<<operand<<"\n";
                    record="";
                    part="";
                    record_index=0;
                    part_index=0;
                    loc = LOCTAB[LOCTAB_INDEX].start_addr;
                    curr_section++;
                    start_loc = LOCTAB[curr_section].start_addr;
                    record_index += sprintf(buff,"%s","T");
                    record+=buff;
                    record_index += sprintf(buff,"%06X",loc);
                    record+=buff;
                    output<<"H"<<setfill(' ')<<setw(6)<<left<<LOCTAB[curr_section].section_name; //stsart the new section with H
                    output<<setfill('0')<<setw(6)<<right<<uppercase<<hex<<LOCTAB[curr_section].start_addr;
                    output<<setfill('0')<<setw(6)<<right<<uppercase<<hex<<LOCTAB[curr_section].length<<"\n";
                }
            }
            else if(opcode=="WORD"){
                bool expr_type=false;
                bool ref_involved = false;
                calculate_expr(operand, &line_index, &expr_type, &ref_involved);
                if(ref_involved){
                    printf("called\n");
                    generate_modification_record(modi_record,operand,modi);
                }
                line_objectCode += line_index;
                sprintf(buff,"%06X",line_objectCode);
                object_code=buff;
                listing<<setfill('0')<<setw(4)<<right<<uppercase<<hex<<loc<<"\t";
                listing<<setfill(' ')<<setw(8)<<left<<label<<" "<<setw(8)<<left<<opcode<<" "<<setw(32)<<left<<operand<<"\t";
                listing<<setfill('0')<<setw(6)<<right<<uppercase<<hex<<line_objectCode<<"\n";
            }
            else if(opcode=="BYTE"){
                line_objectCode=0;
                int tmp_index=0;
                char tmp_ptr[32];
                if( (operand[0]=='C' || operand[0]=='c') && operand[1]=='\''){
                    for (int i = 2; i<=operand.length()-2; i++){
                        line_objectCode += (int)operand[i];
                        line_objectCode<<=8;
                    }
                    line_objectCode>>=8;
                    sprintf(buff,"%X",line_objectCode);
                    object_code+=buff;
                }
                else if( (operand[0]=='X' || operand[0]=='x' ) && operand[1]=='\''){
                    for(int i=2;i<=operand.length()-2;i++ ){
                        tmp_ptr[tmp_index++] = operand[i];
                    }
                    tmp_ptr[tmp_index] = '\0';
                    string c=tmp_ptr;
                    line_objectCode += stringToHex(c);
                    sprintf(buff,"%s",tmp_ptr);
                    object_code+=buff;
                }
                listing<<setfill('0')<<setw(4)<<right<<uppercase<<hex<<loc<<"\t";
                listing<<setfill(' ')<<setw(8)<<left<<label<<" "<<setw(8)<<left<<opcode<<" "<<setw(32)<<left<<operand<<"\t";
                listing<<setfill('0')<<setw(2)<<right<<uppercase<<hex<<line_objectCode<<"\n";
            }
            else{
                if(opcode=="EXTREF"||opcode=="EXTDEF"||opcode=="LTORG"){
                    listing<<"\t\t";
                    listing<<setfill(' ')<<setw(8)<<left<<label<<" "<<setw(8)<<left<<opcode<<" "<<setw(8)<<left<<operand<<"\n";
                }
                else{
                    listing<<setfill('0')<<setw(4)<<right<<uppercase<<hex<<loc<<"\t";
                    listing<<setfill(' ')<<setw(8)<<left<<label<<" "<<setw(8)<<left<<opcode<<" "<<setw(8)<<left<<operand<<"\n";
                }
            }
            if(opcode=="EXTDEF"){ //stores record w.r.t EXTDEF as D records
                define_index=1;
                define_record="D";
                string token="";
                istringstream iss(operand);
                while(getline(iss,token,',')){
                    search_SYMTAB(token);
                    if(SYMTAB_FOUND){
                        char c[200];
                        int n=SYMTAB[SYMTAB_INDEX].symbol.length();
                        for(int i=0;i<n;i++){
                            c[i]=SYMTAB[SYMTAB_INDEX].symbol[i];
                        }
                        c[n]='\0';
                        define_index+=sprintf(buff,"%s",c);
                        define_record+=buff;
                        define_index += sprintf(buff,"%06X",SYMTAB[SYMTAB_INDEX].addr);
                        define_record+=buff;
                    }
                }
                output<<define_record<<"\n";
            }
            else if(opcode=="EXTREF"){ //stores record w.r.t EXTREF as R records
                refer_index=1;
                refer_record="R";
                string token="";
                istringstream iss(operand);
                while(getline(iss,token,',')){
                    char c[200];
                    int n=token.length();
                    for(int i=0;i<n;i++){
                        c[i]=token[i];
                    }
                    c[n]='\0';
                    refer_index+=sprintf(buff,"%-6s",c);
                    refer_record+=buff;
                }
                output<<refer_record<<"\n";
            }
            else if(opcode=="LTORG"|| (object_code.length()+part.length()>60)||(loc-start_loc)>27){
                // If the object code cannot fit into the text record
                //print it out to output and start a new text record
                record_index += sprintf(buff,"%02X",(int)(part.length()/2));
                record+=buff;
                char c[200];
                for(int i=0;i<part.length();i++){
                    c[i]=part[i];
                }
                c[(int)part.length()]='\0';
                record_index += sprintf(buff,"%s",c);
                record+=buff;
                if(part.length()){
                    output<<record<<"\n";
                }
                record="";
                part="";
                record_index=0;
                part_index=0;
                start_loc = loc;
                record_index++;
                record+="T";
                record_index += sprintf(buff,"%06X",loc);
                record+=buff;
            }

            char c[200];
            for(int i=0;i<object_code.length();i++){
                c[i]=object_code[i];
            }
            c[object_code.length()]='\0';
            part_index+=sprintf(buff,"%s",c);
            part+=buff;
        }
        readLinePass2(intermediate);
    }
    listing<<"\t\t";
    listing<<setfill(' ')<<setw(8)<<left<<label<<" "<<setw(8)<<left<<opcode<<" "<<setw(8)<<left<<operand<<"\n";
    while(1){
        readLinePass2(intermediate);
        line_objectCode=0;
        line_opcode=0;
        line_index=0;
        OPTAB_FOUND=0;
        SYMTAB_FOUND=0;
        LITTAB_FOUND=0;
        object_code=tmp_opcode=tmp_operand="";
        tmp_opcode=opcode;
        tmp_operand=operand;
        if(buffer.length()<=1){
            break;
        }
        search_LITTAB(opcode);
        if(LITTAB_FOUND){
            line_objectCode = LITTAB[LITTAB_INDEX].operand_value;
            if(LITTAB[LITTAB_INDEX].name[1]=='X' || LITTAB[LITTAB_INDEX].name[1]=='x'){
                int temp_index=0;
                char temp_ptr[32];
                temp_ptr[0] = '\0';
                for(int i=3;i<=opcode.length()-2;i++ ){
                    temp_ptr[temp_index++] = opcode[i];
                }
                temp_ptr[temp_index] = '\0';
                sprintf(buff,"%s",temp_ptr);
                object_code+=buff;
            }
            else{
                sprintf(buff,"%X",line_objectCode);
                object_code+=buff;
            }
        }
        listing<<setfill('0')<<setw(4)<<right<<uppercase<<hex<<loc<<"\t";
        listing<<setfill(' ')<<setw(8)<<left<<label<<" "<<setw(8)<<left<<opcode<<" "<<setw(32)<<left<<operand<<"\t";
        listing<<setfill('0')<<setw(2)<<right<<uppercase<<hex<<line_objectCode<<"\n";
        part_index += object_code.length();
        part+=object_code; // add object code
    }
    record_index += sprintf(buff,"%02X",(int)part.length()/2);
    record+=buff;
    char c[200];
    for(int i=0;i<part.length();i++){
        c[i]=part[i];
    }
    c[part.length()]='\0';
    record_index += sprintf(buff,"%s",c);
    record+=buff;
    output<<record<<"\n";
    copy_modification_records(modi_record,modi,output);
    output<<"E\n";
    modi.close();
    listing.close();
    output.close();
    intermediate.close();
    cout<<"Pass-2 completed"<<endl;
}

int main(){
    initialize();
    insertValuesOptab();
    insertValuesReg();
    pass1();
    resetForPass2();
    pass2();
    return 0;
}
