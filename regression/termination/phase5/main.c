void main()
{
  int x = 1;  
  int y = 1;  

  while(x>0)
  {
    if(y<10) x++;
    else x--;
    y++; //overflows, hence there is no lexicographical ranking function
  }
  assert(x==0);
}
