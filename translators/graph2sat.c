/* asptools -- Tool collection for answer set programming

   Copyright (C) 2022 Masood Feyzbakhsh Rankooh

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License along
   with this program; if not, write to the Free Software Foundation, Inc.,
   51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
*/

/*
 * GRAPH2SAT -- Translates SAT modulo graphs to pure SAT using Vertex Elimination
 *
 * (c) 2022 Masood Feyzbakhsh Rankooh
 *
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>

#include "version.h"

int **graph;
int **graphAdj;
int *ngraphAdj;
int **graphAdjrev;
int *ngraphAdjrev;
int *deleted;
int nNodes;
int oldnProp;
int oldnCl;
int nCl;
int nProp;
int **g2;
char *program_name = NULL;

void _version_graph2sat_c()
{
  fprintf(stderr, "%s: version information:\n", program_name);
  _version("$RCSfile: graph2sat.c,v $",
	   "$Date: 2022/05/13 11:43:21 $",
	   "$Revision: 1.3 $");

  return;
}

void usage()
{
  fprintf(stderr, "\nusage:");
  fprintf(stderr, "   graph2sat <options> <file>\n\n");
  fprintf(stderr, "options:\n");
  fprintf(stderr, "   -h or --help -- print help message\n");
  fprintf(stderr, "   --version -- print version information\n");
  fprintf(stderr, "\n");
  
  return;
}




static inline int graphEdge(int x1,int x2){

  int result;
  if (x1<=x2){
    if (g2[x1][x2]==-1){
      nProp++;
      g2[x1][x2]=nProp;
    }
    result =g2[x1][x2];   
  }
  else{
    if (g2[x2][x1]==-1){
      nProp++;
      g2[x2][x1]=nProp;
    }
    result =-g2[x2][x1];  
  }

  
  return(result);

  
}
int main(int argc,char **argv) {
  char *in;
  FILE *infile;
  char out[1000];
  FILE *outfile= stdout;
  
  int option_help = 0;
  int option_version = 0;
  char *arg = NULL;
  int which = 0;
  int error = 0;

  program_name = argv[0];

  for(which=1; which<argc; which++) {
    arg = argv[which];
    
    if(strcmp(arg, "-h") == 0 || strcmp(arg, "--help") == 0)
      option_help = -1;
    else if(strcmp(arg, "--version") == 0)
      option_version = -1;
    else if(in == NULL)
      in = arg;
    else {
      fprintf(stderr, "unknown argument %s\n", arg);
      error = -1;
    }
    
  }
  
  if(option_help) usage();
  if(option_version) _version_graph2sat_c();
  
  if(option_help || option_version)
    exit(0);
  
  if(error) {
    usage();
    exit(-1);
  }
  
  /* Read in logic program */
  
  if(in == NULL)
    in = "-";
  
  if(strcmp("-", in) == 0) {
    infile = stdin;
  } else {
    if((infile = fopen(in, "r")) == NULL) {
      fprintf(stderr, "cannot open file %s\n", in);
      exit(-1);
    }
  }
  

    
    char line[10000];
    
    while (fgets(line, 10000, infile))
    {
      if (line[0]=='p' && (line[1]==' ')){
        char p[80];
        char cnf[80];
        sscanf(line,"%s%s%d%d",p,cnf,&oldnProp,&oldnCl);
        
        nProp = oldnProp;
        nCl = oldnCl;
      }
      

      if (line[0]=='c' && (line[1]==' '))
      {
        if (line[2]=='g'){

          fprintf(outfile,"c *************************\n");
          
          
          fprintf(outfile,"c *************************\n");
          
          
          fprintf(outfile,"c *************************\n");
          
          fprintf(outfile,"c *************************\n");

          char c[80];
          char g[80];
          sscanf(line,"%s%s%d",c,g,&nNodes);
          nNodes++;
          g2 = (int **)malloc(nNodes * sizeof(int *));
          for (int i=0; i<nNodes;i++){
            g2[i] = (int *)malloc(nNodes * sizeof(int));
            for (int j=0; j<nNodes;j++){
              g2[i][j]=-1;
            }
            
          }
          graph = (int **)malloc(nNodes * sizeof(int *));
          graphAdj = (int **)malloc(nNodes * sizeof(int *));
          graphAdjrev = (int **)malloc(nNodes * sizeof(int *));
          ngraphAdj=(int *)malloc((nNodes) * sizeof(int));
          ngraphAdjrev=(int *)malloc((nNodes) * sizeof(int));
          deleted=(int *)malloc((nNodes) * sizeof(int));
          for(int i=0;i<nNodes;i++){
            ngraphAdj[i]=-1;
            ngraphAdj[i]=0;
            ngraphAdjrev[i]=0;
            graph[i]=(int *)malloc((nNodes) * sizeof(int));
            graphAdj[i]=(int *)malloc((nNodes) * sizeof(int));
            graphAdjrev[i]=(int *)malloc((nNodes) * sizeof(int));
            for (int j=0;j<nNodes;j++){
              graph[i][j]= -1;
              graphAdj[i][j]= -1;
              graphAdjrev[i][j]= -1;
            }

          }
          continue;
        }
        if (line[2]=='n'){
          continue;
        }
        if (line[2]=='a'){
          if (line[3]=='r'){
            char c[80];
            char arc[80];
            int v;
            int s;
            int t;
            
            sscanf(line,"%s%s%d%d%d",c,arc,&v,&s,&t);
            if (graph[s][t]!=-1)
              continue;
            if (s==t){
              //fprintf(outfile,"%d 0\n",-v);
              //nCl++;
              //continue;
            }
              
            graph[s][t]=v;
            graphAdj[s][ngraphAdj[s]]=t;
            ngraphAdj[s]++;
            graphAdjrev[t][ngraphAdjrev[t]]=s;
            ngraphAdjrev[t]++;
            
            continue;
          }
                     
        }
        if (line[2]=='e'){
          

          
          for (int i=0;i<nNodes;i++){
            for (int j=0;j<ngraphAdj[i];j++){
              
              int e =graph[i][graphAdj[i][j]];

              fprintf(outfile,"%d %d 0\n",-e,graphEdge(i,graphAdj[i][j]));
              
              nCl++;

              
            }
          }
    
          
          int degreesOut[nNodes];
          int degreesIn[nNodes];
          for (int i=0; i<nNodes; i++){
            degreesOut[i]=0;
            degreesIn[i]=0;
          }
          
          for (int i=0; i<nNodes; i++){
            
            degreesOut[i]=ngraphAdj[i];
            degreesIn[i]=ngraphAdjrev[i];
            
          }
          
          for (int c=0; c<nNodes; c++){
            int mindegree=100000000;
            int minv =-1;
            for (int j=0; j<nNodes; j++){
              if (deleted[j]==1)
                continue;
              if (degreesIn[j]*degreesOut[j]<mindegree){
                mindegree=degreesIn[j]*degreesOut[j];
                minv=j;
              }

            }

            if (argc>1)
            printf("\n%d %d", c, degreesOut[minv]);
            
            deleted[minv]=1;
            int i=minv;
            for (int a=0; a<ngraphAdjrev[i]; a++){
              int j=graphAdjrev[i][a];
              if (deleted[j]==1)
                continue;

              for (int b=0; b<ngraphAdj[i]; b++){
                int k=graphAdj[i][b];
                if (deleted[k]==1)
                  continue;

                
                if (graph[j][k]==-1){
                  
                  if (j!=k){
                    graph[j][k]=graphEdge(j,k);
                    graphAdj[j][ngraphAdj[j]]=k;
                    ngraphAdj[j]++;
                    graphAdjrev[k][ngraphAdjrev[k]]=j;
                    ngraphAdjrev[k]++; 
                    degreesIn[k]++;
                    degreesOut[j]++;
                  }
                  
                } 
                
                
                fprintf(outfile,"%d %d %d 0\n",-graphEdge(j,i),-graphEdge(i,k),graphEdge(j,k));
                nCl++;
                
              }
            }
            for (int b=0; b<ngraphAdj[i]; b++){
              int k=graphAdj[i][b];
              if (deleted[k]==1)
                continue;
              degreesOut[i]--;
              
              degreesIn[k]--;
            }
            for (int b=0; b<ngraphAdjrev[i]; b++){
              int k=graphAdjrev[i][b];
              if (deleted[k]==1)
                continue;
              degreesOut[k]--;
              
              degreesIn[i]--;
            }

            
            



                  
          }

          for (int i=0; i<nNodes; i++){
            for (int k=i; k<nNodes; k++){
              if ((graph[i][k]!=-1) && (graph[k][i]!=-1)){
                fprintf(outfile,"%d %d 0\n",-graphEdge(i,k),-graphEdge(k,i));
                nCl++;
              }
            }
          }
          
          
          
          
          
        } 
        
        continue;
      }

        
      fprintf(outfile,"%s",line);
      

    }
    


  fclose(infile);
  fclose(outfile);
  /*
  if (argc>1){
    outfile = fopen(out, "r+");
    int dummy;
    fprintf(outfile,"p cnf %d %d\n",nProp,nCl);
    if ((oldnProp!=nProp) || (oldnCl!=nCl))
      fprintf(outfile,"c ");
    
    
    
    
    fclose(outfile);
  }
  */
 return 0;
}
