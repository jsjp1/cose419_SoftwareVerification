/*
 * GccApplication2.c
 *
 * Created: 7/3/2023 7:19:17 PM
 * Author : suhtw
 */ 

#pragma GCC target ("thumb")

#include "sam.h"

extern int lab_asm_port_test();
extern int lab_asm_func_test();

void print_decimal(unsigned int);
void print_enter();

void GCLK_setup();
void USART_setup();
void RTC_setup();
void PORT_setup();
void TC3_setup();
void TC4_setup();
void EIC_setup();
void direction();
unsigned int Distance();


unsigned int dist = 10;
unsigned int pre_dist = 10; // 현재 dist의 값이 잘못 측정된건 아닌지 판단하기 위해

unsigned int left_motor_speed = 175;
unsigned int right_motor_speed = 175;

int left_black = 1;
int middle_black = 0;
int right_black = 1;
int main()
{
    int i;
      
   /* Initialize the SAM system */
    SystemInit();
   
   GCLK_setup();
   
   USART_setup();

   PORT_setup();
   
   TC3_setup();
   TC4_setup();
   
   EIC_setup();
   
   
   NVIC->ISER[0] = 1 << 4;
   NVIC->IP[1] = 0x40 << 0;

   while (1) {
      // ----------------------------------------------
      // 10 usec pulse to Trigger input in Ultrasonic sensor
      // --------------------------------------------
      PORT->Group[0].OUT.reg = 0 << 8 ;
   
      RTC_setup();
   
      while (RTC->MODE0.INTFLAG.bit.CMP0 != 1) ;
      RTC->MODE0.INTFLAG.bit.CMP0 = 1; // clear overflow interrupt flag
      PORT->Group[0].OUT.reg = 1 << 8;   
      while (RTC->MODE0.INTFLAG.bit.CMP0 != 1) ;

      RTC->MODE0.INTFLAG.bit.CMP0 = 1; // clear overflow interrupt flag
      PORT->Group[0].OUT.reg = 0 << 8 ;
      // --------------------------------------------

      // Now use RTC to measure the pulse width of echo input.
      RTC->MODE0.CTRL.bit.ENABLE = 0; // Disable first
      RTC->MODE0.CTRL.bit.MATCHCLR = 0; // Now just count...
      RTC->MODE0.COUNT.reg = 0x0; // initialize the counter to 0
      RTC->MODE0.CTRL.bit.ENABLE = 1; // Enable   
   
      // direction(); // 방향을 바꾸기 위해 인터럽트 발생시 바뀌는 세개의 값에 의해 조절
      
      
      /*
      // Measure the distance   
      unsigned int diff = (pre_dist > dist) ? (pre_dist - dist) : (dist - pre_dist);
      if(diff > 8){
         pre_dist = 10;
         for (i= 0; i<750000; i++ ) ;  // idle roughly for 0.5 second
         continue;
      }
      
      if(dist <= 8){
         pre_dist = dist;
         TC3->COUNT16.CC[1].reg = 150;
         TC4->COUNT16.CC[1].reg = 150;
      }else if(dist > 8 && dist <= 15){
         pre_dist = dist;
         TC3->COUNT16.CC[1].reg = 200;
         TC4->COUNT16.CC[1].reg = 200;
      }else if(dist > 15 && dist <= 23){
         pre_dist = dist;
         TC3->COUNT16.CC[1].reg = 300;
         TC4->COUNT16.CC[1].reg = 300;
      }else if(dist > 23 && dist <= 30){
         pre_dist = dist;
         TC3->COUNT16.CC[1].reg = 350;
         TC4->COUNT16.CC[1].reg = 350;
      }else{
         // :10 과 같이 잘못된 값이 나오는경우
         continue;
      }
      */
   
      for (i= 0; i<750000; i++ ) ;  // idle roughly for 0.5 second
   };

   return (0);
}


void GCLK_setup() {
   
   // OSC8M
   //SYSCTRL->OSC8M.bit.ENABLE = 0; // Disable
   SYSCTRL->OSC8M.bit.PRESC = 0;  // prescaler to 1
   SYSCTRL->OSC8M.bit.ONDEMAND = 0; 
   //SYSCTRL->OSC8M.bit.ENABLE = 1; // Enable

   //
   // Generic Clock Controller setup for RTC
   // * RTC ID: #4 
   // * Generator #0 is feeding RTC
   // * Generator #0 is taking the clock source #6 (OSC8M: 8MHz clock input) as an input

   GCLK->GENCTRL.bit.ID = 0; // Generator #0
   GCLK->GENCTRL.bit.SRC = 6; // OSC8M
   GCLK->GENCTRL.bit.OE = 1 ;  // Output Enable: GCLK_IO
   GCLK->GENCTRL.bit.GENEN = 1; // Generator Enable
   
   GCLK->CLKCTRL.bit.ID = 4; // ID #4 (RTC)
   GCLK->CLKCTRL.bit.GEN = 0; // Generator #0 selected for RTC
   GCLK->CLKCTRL.bit.CLKEN = 1; // Now, clock is supplied to RTC!   
   
   GCLK->CLKCTRL.bit.ID = 5; // ID #5 (EIC)
   GCLK->CLKCTRL.bit.GEN = 0; // Generator #0 selected for RTC
   GCLK->CLKCTRL.bit.CLKEN = 1; // Now, clock is supplied to RTC!

   GCLK->CLKCTRL.bit.ID = 0x1B; // ID #ID (TCC2, TC3)
   GCLK->CLKCTRL.bit.GEN = 0; // Generator #0 selected for TCC2, TC3
   GCLK->CLKCTRL.bit.CLKEN = 1; // Now, clock is supplied to TCC2, TC3
      
   GCLK->CLKCTRL.bit.ID = 0x1C; // ID #ID (TC4, TC5)
   GCLK->CLKCTRL.bit.GEN = 0; // Generator #0 selected for TC4, TC5
   GCLK->CLKCTRL.bit.CLKEN = 1; // Now, clock is supplied to TC4, TC5
}


void PORT_setup() {
   
   //
   // PORT setup for PA14 (GCLK_IO[0]) to check out clock output using logic analyzer
   //
   PORT->Group[0].PINCFG[14].reg = 0x41;      // peripheral mux: DRVSTR=1, PMUXEN = 1
   PORT->Group[0].PMUX[7].bit.PMUXE = 0x07;   // peripheral function H selected
   
   // ********************** LINE TRACKING SENSOR ********************************
   PORT->Group[0].PINCFG[17].reg = 0x0;
   PORT->Group[0].DIR.reg = 0x1 << 17;
   
   PORT->Group[0].PINCFG[6].reg = 0x3; // middle
   PORT->Group[0].PINCFG[6].reg = 0x41; // middle
   PORT->Group[0].PMUX[3].bit.PMUXE = 0x0;
   PORT->Group[0].PINCFG[7].reg = 0x3; // left
   PORT->Group[0].PINCFG[7].reg = 0x41; // left
   PORT->Group[0].PMUX[3].bit.PMUXO = 0x0;
   PORT->Group[0].PINCFG[18].reg = 0x3; // right
   PORT->Group[0].PINCFG[18].reg = 0x41; // right
   PORT->Group[0].PMUX[9].bit.PMUXE = 0x0;
   // ********************** LINE TRACKING SENSOR ********************************


   // ********************** UNLTRA SONIC SENSOR ********************************
   // Trigger in Ultrasonic Sensor
   PORT->Group[0].PINCFG[8].reg = 0x0;      // PMUXEN = 0
   PORT->Group[0].DIRSET.reg = 0x1 << 8;      // Direction: Output
   PORT->Group[0].OUT.reg = 0 << 8 ;          // Set the Trigger to 0

   // PORT setup for PA09 to take the echo input from Ultrasonic sensor
   PORT->Group[0].PINCFG[9].reg = 0x41;      // INEN = 1, PMUXEN = 0
   PORT->Group[0].PMUX[4].bit.PMUXO = 0x0;
   // ********************** UNLTRA SONIC SENSOR ********************************
}



void TC3_setup() {
   // PORT setup for PA19 ( TC3's WO[1] )
   PORT->Group[0].PINCFG[19].reg = 0x41;      // peripheral mux: DRVSTR=1, PMUXEN = 1
   PORT->Group[0].PMUX[9].bit.PMUXO = 0x04;   // peripheral function E selected

   // Power Manager
   PM->APBCMASK.bit.TC3_ = 1 ; // Clock Enable (APBC clock) for TC3
   
   // TC3 setup: 16-bit Mode
   TC3->COUNT16.CTRLA.bit.MODE = 0;  // Count16 mode
   TC3->COUNT16.CTRLA.bit.WAVEGEN = 3 ; // Match PWM (MPWM)
   TC3->COUNT16.CTRLA.bit.PRESCALER = 6; // Timer Counter clock 31,250 Hz = 8MHz / 256
   //TC3->COUNT16.CC[0].reg = 30000;  // CC0 defines the period
   //TC3->COUNT16.CC[1].reg = 10000;  // CC1 match pulls down WO[1]
   TC3->COUNT16.CC[0].reg = 1000;  // CC0 defines the period
   TC3->COUNT16.CC[1].reg = 300;  // CC1 match pulls down WO[1]
   TC3->COUNT16.CTRLA.bit.ENABLE = 1 ;
}


void TC4_setup() {
   // PORT setup for PB09 ( TC4's WO[1] )
   PORT->Group[1].PINCFG[9].reg = 0x41;      // peripheral mux: DRVSTR=1, PMUXEN = 1
   PORT->Group[1].PMUX[4].bit.PMUXO = 0x04;   // peripheral function E selected

   // Power Manager
   PM->APBCMASK.bit.TC4_ = 1 ; // Clock Enable (APBC clock) for TC3

   // TC4 setup: 16-bit Mode
   TC4->COUNT16.CTRLA.bit.MODE = 0;  // Count16 mode
   TC4->COUNT16.CTRLA.bit.WAVEGEN = 3 ; // Match PWM (MPWM)
   TC4->COUNT16.CTRLA.bit.PRESCALER = 6; // Timer Counter clock 31,250 Hz = 8MHz / 256
   //TC3->COUNT16.CC[0].reg = 30000;  // CC0 defines the period
   //TC3->COUNT16.CC[1].reg = 10000;  // CC1 match pulls down WO[1]
   TC4->COUNT16.CC[0].reg = 1000;  // CC0 defines the period
   TC4->COUNT16.CC[1].reg = 300;  // CC1 match pulls down WO[1]
   TC4->COUNT16.CTRLA.bit.ENABLE = 1 ;
}


void EIC_setup() {
   EIC->CONFIG[1].bit.FILTEN1 = 1;
   EIC->CONFIG[1].bit.SENSE1 = 0x3;
   EIC->INTENSET.bit.EXTINT9 = 1;
   
   
   // 0x1 : 흰선 -> 검은선
   // 0x2 : 검은선 -> 흰선 
   // 0x3 : 흰선 -> 검은선 && 검은선 -> 흰선
   
   // Configure sense and filter for EXTINT[6], EXTINT[7], EXTINT[2]
   EIC->CONFIG[0].bit.FILTEN6 = 1;    // Filter is enabled for EXTINT[6]
   EIC->CONFIG[0].bit.SENSE6 = 0x3;   // Both-edges detection for EXTINT[6]
   EIC->INTENSET.bit.EXTINT6 = 1;
   
   EIC->CONFIG[0].bit.FILTEN7 = 1;    // Filter is enabled for EXTINT[7]
   EIC->CONFIG[0].bit.SENSE7 = 0x3;   // Both-edges detection for EXTINT[7]
   EIC->INTENSET.bit.EXTINT7 = 1;
   
   EIC->CONFIG[0].bit.FILTEN2 = 1;    // Filter is enabled for EXTINT[2]
   EIC->CONFIG[0].bit.SENSE2 = 0x3;   // Both-edges detection for EXTINT[2]
   EIC->INTENSET.bit.EXTINT2 = 1;
   
   
   EIC->CTRL.bit.ENABLE = 1;
}


void RTC_setup() {
   // RTC setup: MODE0 (32-bit counter) with COMPARE 0
   RTC->MODE0.CTRL.bit.ENABLE = 0; // Disable first
   RTC->MODE0.CTRL.bit.MODE = 0; // Mode 0
   RTC->MODE0.CTRL.bit.MATCHCLR = 1; // match clear
   
   // 8MHz RTC clock  --> 10 usec when 80 is counted
   RTC->MODE0.COMP->reg = 80; // compare register to set up 10usec interval 
   RTC->MODE0.COUNT.reg = 0x0; // initialize the counter to 0
   RTC->MODE0.CTRL.bit.ENABLE = 1; // Enable
}

void direction(void){
   // 0 -> 검은색 위, 1 -> 흰색 위
   int total = 100*middle_black + 10*left_black + right_black;
   
   switch(total){
      case 11: // 가운데만 검은선 위
         left_motor_speed = 200;
         right_motor_speed = 200;
         break;
      case 101: // 왼쪽만 검은색 위
         left_motor_speed = 150;
         right_motor_speed = 0;
         break;
      case 110: // 오른쪽만 검은색 위
         left_motor_speed = 150;
         right_motor_speed = 0;
      default:
         break;
   }
}

unsigned int RTC_count, count_start, count_end;
unsigned int Num_EIC_interrupts = 0;

void EIC_Handler(void)
{
   if(EIC->INTFLAG.bit.EXTINT9){ // ULTRA SONIC SENSOR
      unsigned int echo_time_interval, distance;
      
      EIC->INTFLAG.bit.EXTINT9 = 1 ; // Clear the EXTINT9 interrupt flag
      Num_EIC_interrupts++;
         
      if      (Num_EIC_interrupts == 1) {
         count_start = RTC->MODE0.COUNT.reg;
      }
      else if (Num_EIC_interrupts == 2) {
            
         count_end   = RTC->MODE0.COUNT.reg;
         RTC_count = count_end - count_start;
         echo_time_interval = RTC_count / 8 ; // echo interval in usec (8MHz clock input)
         distance = (echo_time_interval / 2) * 0.034 ; // distance in cm
            
         dist = distance;
            /*
         print_decimal(distance / 100);
         distance = distance % 100;
         print_decimal(distance / 10);
         print_decimal(distance % 10);
         print_enter();
         Num_EIC_interrupts = 0 ;
         */
      }
   }

   if(EIC->INTFLAG.bit.EXTINT6){
      // Middle
      EIC->INTFLAG.bit.EXTINT6 = 1 ; // Clear the EXTINT6 interrupt flag
      if(middle_black == 0){ // 흰 -> 검
         middle_black = 1;
      }else{ // 검 -> 흰
         middle_black = 0;
      }
   }
         
   if(EIC->INTFLAG.bit.EXTINT7){ // ULTRA SONIC SENSOR
      // right
      EIC->INTFLAG.bit.EXTINT7 = 1 ; // Clear the EXTINT7 interrupt flag
      if(right_black == 1){ // 흰 -> 검
         right_black = 0;
      }else{ // 검 -> 흰
         right_black = 1;
      }
   }
         
   if(EIC->INTFLAG.bit.EXTINT2){ // ULTRA SONIC SENSOR
      // left
      EIC->INTFLAG.bit.EXTINT2 = 1 ; // Clear the EXTINT2 interrupt flag
      if(left_black == 1){ // 흰 -> 검
         left_black = 0;
      }else{ // 검 -> 흰
         left_black = 1;
      }
      //PORT->Group[0].OUT.reg |= 0x1 << 17;
   }

   direction();

   TC3->COUNT16.CC[1].reg = left_motor_speed;
   TC4->COUNT16.CC[1].reg = right_motor_speed;
}

void USART_setup() {
   
   //
   // PORT setup for PB22 and PB23 (USART)
   //
   PORT->Group[1].PINCFG[22].reg = 0x41; // peripheral mux: DRVSTR=1, PMUXEN = 1
   PORT->Group[1].PINCFG[23].reg = 0x41; // peripheral mux: DRVSTR=1, PMUXEN = 1

   PORT->Group[1].PMUX[11].bit.PMUXE = 0x03; // peripheral function D selected
   PORT->Group[1].PMUX[11].bit.PMUXO = 0x03; // peripheral function D selected

   // Power Manager
   PM->APBCMASK.bit.SERCOM5_ = 1 ; // Clock Enable (APBC clock) for USART
   
   //
   // * SERCOM5: USART
   // * Generator #0 is feeding USART as well
   //
   GCLK->CLKCTRL.bit.ID = 0x19; // ID #0x19 (SERCOM5: USART): GCLK_SERCOM3_CORE
   GCLK->CLKCTRL.bit.GEN = 0; // Generator #0 selected for USART
   GCLK->CLKCTRL.bit.CLKEN = 1; // Now, clock is supplied to USART!

   GCLK->CLKCTRL.bit.ID = 0x13; // ID #0x13 (SERCOM5: USART): GCLK_SERCOM_SLOW
   GCLK->CLKCTRL.bit.GEN = 0; // Generator #0 selected for USART
   GCLK->CLKCTRL.bit.CLKEN = 1; // Now, clock is supplied to USART!
   
   //
   // USART setup
   //
   SERCOM5->USART.CTRLA.bit.MODE = 1 ; // Internal Clock
   SERCOM5->USART.CTRLA.bit.CMODE = 0 ; // Asynchronous UART
   SERCOM5->USART.CTRLA.bit.RXPO = 3 ; // PAD3
   SERCOM5->USART.CTRLA.bit.TXPO = 1 ; // PAD2
   SERCOM5->USART.CTRLB.bit.CHSIZE = 0 ; // 8-bit data
   SERCOM5->USART.CTRLA.bit.DORD = 1 ; // LSB first
   //SERCOM5->USART.CTRLA.bit.SAMPR = 1 ; //

   SERCOM5->USART.BAUD.reg = 0Xc504 ; // 115,200 bps (baud rate) with 8MHz input clock
   //SERCOM5->USART.BAUD.reg = 0Xe282 ; // 115,200 bps (baud rate) with 16MHz input clock
   //SERCOM5->USART.BAUD.reg = 0Xec57 ; // 115,200 bps (baud rate) with 24MHz input clock
   //SERCOM5->USART.BAUD.reg = 0Xf62b ; // 115,200 bps (baud rate) with 48MHz input clock

   SERCOM5->USART.CTRLB.bit.RXEN = 1 ;
   SERCOM5->USART.CTRLB.bit.TXEN = 1 ;

   SERCOM5->USART.CTRLA.bit.ENABLE = 1;
   
}


void print_decimal(unsigned int data) {

   unsigned char conv_data;

   while (SERCOM5->USART.INTFLAG.bit.DRE != 1) ; // DRE (Data Register Empty) is set when DATA is empty

   conv_data = (unsigned char) (data & 0x000000FF)  ; // 
   conv_data += 48 ; // 0, 1, ... 9
   
   SERCOM5->USART.DATA.reg   = conv_data ; // transmit the first number (ASCII code)
   
};

void print_enter() {

   while (SERCOM5->USART.INTFLAG.bit.DRE != 1) ; // DRE (Data Register Empty) is set when DATA is empty
   SERCOM5->USART.DATA.reg   = 10 ; // transmit LF (Line Feed)
   //
   while (SERCOM5->USART.INTFLAG.bit.DRE != 1) ;
   SERCOM5->USART.DATA.reg   = 13 ; // transmit CR (Carriage Return)
};
